"""
Panchang — a single-file, mobile-first Flask web application.

Everything required by the app (HTML, CSS, JavaScript, API routes, PWA shell,
SEO metadata and Panchang calculations) lives in this file.  The astronomical
engine is Swiss Ephemeris through pyswisseph, using Lahiri ayanamsa and the
built-in Moshier ephemeris so no separate ephemeris files are required.

Production command (Render):
    gunicorn --bind 0.0.0.0:$PORT panchang:app

Daily push cron command (run every minute):
    python panchang.py send-daily-push

License note: pyswisseph is AGPL-3.0. If this application is published as a
network service, review and comply with the Swiss Ephemeris/pyswisseph license.
"""

from __future__ import annotations

import base64
import glob
import hashlib
import html
import io
import json
import math
import os
import re
import secrets
import sqlite3
import sys
import threading
import unicodedata
from datetime import date, datetime, time as dt_time, timedelta, timezone
from contextlib import contextmanager
from functools import lru_cache
from typing import Any, Callable, Iterable
from urllib.parse import quote, urlencode, urlsplit
from zoneinfo import ZoneInfo, ZoneInfoNotFoundError

import requests
import swisseph as swe

try:
    from PIL import Image, ImageDraw, ImageFilter, ImageFont
except Exception:  # The static embedded social image remains a safe fallback.
    Image = ImageDraw = ImageFilter = ImageFont = None
from flask import Flask, Response, jsonify, make_response, redirect, request
from jinja2 import BaseLoader, Environment, select_autoescape
from werkzeug.middleware.proxy_fix import ProxyFix

try:
    from indic_transliteration import sanscript
    from indic_transliteration.sanscript import transliterate
except Exception:  # The app still works in English if optional transliteration fails.
    sanscript = None
    transliterate = None

try:
    import psycopg
    from psycopg.rows import dict_row as psycopg_dict_row
except Exception:  # SQLite remains available for local or persistent-disk deployments.
    psycopg = None
    psycopg_dict_row = None

try:
    from pywebpush import WebPushException, webpush
except Exception:  # The page remains usable when push dependencies are not installed.
    WebPushException = Exception
    webpush = None

try:
    from cryptography.hazmat.primitives import serialization
    from cryptography.hazmat.primitives.asymmetric import ec
except Exception:  # pywebpush normally supplies cryptography as a dependency.
    serialization = None
    ec = None


app = Flask(__name__)
# Render terminates HTTPS before forwarding the request. Trust its single proxy
# hop so canonical, Open Graph and sitemap URLs are emitted with the public
# HTTPS host rather than an internal HTTP URL.
app.wsgi_app = ProxyFix(app.wsgi_app, x_for=1, x_proto=1, x_host=1, x_port=1)
app.config.update(JSON_SORT_KEYS=False, MAX_CONTENT_LENGTH=32 * 1024, PREFERRED_URL_SCHEME="https")

APP_NAME = os.getenv("PANCHANG_APP_NAME", "Panchang")
APP_VERSION = "2.2.0"

# All public, shareable and crawler-facing URLs use the custom domain.  Render's
# temporary hostname is intentionally never exposed in canonical, Open Graph,
# sitemap or browser-share URLs.  PUBLIC_SITE_URL can override this for another
# production domain; SITE_URL remains supported for existing deployments.
def _configured_public_site_url() -> str:
    raw = (os.getenv("PUBLIC_SITE_URL") or os.getenv("SITE_URL") or "https://panchangworld.com").strip().rstrip("/")
    if not re.match(r"^https?://", raw, flags=re.IGNORECASE):
        raw = f"https://{raw}"
    parsed = urlsplit(raw)
    host = (parsed.hostname or "").lower()
    if not host or host.endswith(".onrender.com"):
        return "https://panchangworld.com"
    scheme = "https" if host not in {"localhost", "127.0.0.1", "::1"} else (parsed.scheme or "http")
    port = f":{parsed.port}" if parsed.port else ""
    return f"{scheme}://{host}{port}"


PUBLIC_SITE_URL = _configured_public_site_url()
DEFAULT_PLACE = {
    "name": "Ujjain",
    "latitude": 23.1765,
    "longitude": 75.7885,
    "timezone": "Asia/Kolkata",
    "country": "India",
}
TIMELINE_PAST_ITEMS = 4
TIMELINE_FUTURE_ITEMS = 12

# Daily Web Push configuration. A stable PUSH_SECRET and persistent database are
# intentionally required in production; changing either one invalidates saved
# subscriptions. Render Postgres should be supplied through DATABASE_URL.
PUSH_HOUR_LOCAL = 7
PUSH_OFFER_AFTER_DAYS = 7
PUSH_DELIVERY_WINDOW_HOURS = 4
PUSH_RETRY_MINUTES = 15
PUSH_CLAIM_MINUTES = 10
PUSH_DATABASE_URL = (os.getenv("PUSH_DATABASE_URL") or os.getenv("DATABASE_URL") or "").strip()
PUSH_SQLITE_PATH = os.getenv("PUSH_DB_PATH", "").strip()
PUSH_SECRET = (os.getenv("PUSH_SECRET") or os.getenv("SECRET_KEY") or "").strip()
PUSH_VAPID_PRIVATE_KEY = os.getenv("VAPID_PRIVATE_KEY", "").replace("\\n", "\n").strip()
PUSH_VAPID_PUBLIC_KEY = os.getenv("VAPID_PUBLIC_KEY", "").strip()
PUSH_VAPID_SUBJECT = (
    os.getenv("VAPID_SUBJECT")
    or PUBLIC_SITE_URL
    or "mailto:admin@example.com"
).strip()
PUSH_CSRF_COOKIE = "panchang_push_csrf"
try:
    PUSH_MAX_BATCH = max(1, min(5000, int(os.getenv("PUSH_MAX_BATCH", "1000"))))
except (TypeError, ValueError):
    PUSH_MAX_BATCH = 1000

UTC = timezone.utc
IST = ZoneInfo("Asia/Kolkata")
ASTRO_FLAGS = swe.FLG_MOSEPH | swe.FLG_SPEED | swe.FLG_SIDEREAL
RISE_SET_FLAGS = swe.FLG_MOSEPH
swe.set_ephe_path("")
swe.set_sid_mode(swe.SIDM_LAHIRI, 0.0, 0.0)


# ---------------------------------------------------------------------------
# Daily Web Push support
# ---------------------------------------------------------------------------

_PUSH_DB_INITIALIZED = False
_PUSH_DB_INIT_LOCK = threading.Lock()
_P256_ORDER = int("FFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551", 16)


def _urlsafe_b64(data: bytes) -> str:
    return base64.urlsafe_b64encode(data).rstrip(b"=").decode("ascii")


def _decode_urlsafe_b64(value: str) -> bytes:
    """Decode padded or unpadded URL-safe Base64 after removing whitespace."""
    compact = re.sub(r"\s+", "", value or "")
    compact += "=" * (-len(compact) % 4)
    return base64.urlsafe_b64decode(compact.encode("ascii"))


def _load_vapid_private_value(value: str) -> tuple[Any, str]:
    """Return (private-key object, pywebpush-compatible value).

    pywebpush accepts either a filesystem path to a PEM key or a Base64URL
    encoded raw/DER private key. Environment variables commonly contain PEM
    text, so those are normalized to a Base64URL PKCS#8 DER string.
    """
    if not value or serialization is None or ec is None:
        return None, ""

    if os.path.isfile(value):
        try:
            with open(value, "rb") as key_file:
                key_bytes = key_file.read()
            key_obj = serialization.load_pem_private_key(key_bytes, password=None)
            if not isinstance(key_obj, ec.EllipticCurvePrivateKey):
                return None, ""
            return key_obj, value
        except (OSError, TypeError, ValueError):
            return None, ""

    if "-----BEGIN" in value:
        try:
            key_obj = serialization.load_pem_private_key(value.encode("utf-8"), password=None)
            if not isinstance(key_obj, ec.EllipticCurvePrivateKey):
                return None, ""
            der = key_obj.private_bytes(
                encoding=serialization.Encoding.DER,
                format=serialization.PrivateFormat.PKCS8,
                encryption_algorithm=serialization.NoEncryption(),
            )
            return key_obj, _urlsafe_b64(der)
        except (TypeError, ValueError):
            return None, ""

    try:
        decoded = _decode_urlsafe_b64(value)
        if len(decoded) == 32:
            scalar = int.from_bytes(decoded, "big")
            if not 1 <= scalar < _P256_ORDER:
                return None, ""
            key_obj = ec.derive_private_key(scalar, ec.SECP256R1())
        else:
            key_obj = serialization.load_der_private_key(decoded, password=None)
        if not isinstance(key_obj, ec.EllipticCurvePrivateKey):
            return None, ""
        # Re-encode so py-vapid receives canonical URL-safe Base64 regardless
        # of whether the supplied value used padding or standard Base64 chars.
        return key_obj, _urlsafe_b64(decoded)
    except (TypeError, ValueError, UnicodeError, base64.binascii.Error):
        return None, ""


@lru_cache(maxsize=1)
def push_vapid_config() -> dict[str, str]:
    """Return a stable VAPID key pair without exposing it to page output."""
    private_key_obj, private_value = _load_vapid_private_value(PUSH_VAPID_PRIVATE_KEY)
    public_value = PUSH_VAPID_PUBLIC_KEY

    if private_key_obj is None and PUSH_SECRET and ec is not None and serialization is not None:
        digest = hashlib.sha256(PUSH_SECRET.encode("utf-8")).digest()
        scalar = (int.from_bytes(digest, "big") % (_P256_ORDER - 1)) + 1
        private_key_obj = ec.derive_private_key(scalar, ec.SECP256R1())
        private_der = private_key_obj.private_bytes(
            encoding=serialization.Encoding.DER,
            format=serialization.PrivateFormat.PKCS8,
            encryption_algorithm=serialization.NoEncryption(),
        )
        private_value = _urlsafe_b64(private_der)

    if not public_value and private_key_obj is not None and serialization is not None:
        point = private_key_obj.public_key().public_bytes(
            encoding=serialization.Encoding.X962,
            format=serialization.PublicFormat.UncompressedPoint,
        )
        public_value = _urlsafe_b64(point)

    subject = PUSH_VAPID_SUBJECT
    if subject and not re.match(r"^(?:mailto:|https?://)", subject, flags=re.IGNORECASE):
        subject = f"https://{subject.lstrip('/')}"

    return {"private": private_value, "public": public_value, "subject": subject}


def push_feature_enabled() -> bool:
    vapid = push_vapid_config()
    storage_ready = bool(PUSH_DATABASE_URL or PUSH_SQLITE_PATH)
    postgres_ready = not PUSH_DATABASE_URL.lower().startswith(("postgres://", "postgresql://")) or psycopg is not None
    return bool(webpush and ec and serialization and vapid["private"] and vapid["public"] and storage_ready and postgres_ready)


def _push_db_backend() -> str:
    return "postgres" if PUSH_DATABASE_URL.lower().startswith(("postgres://", "postgresql://")) else "sqlite"


def _push_sql(sql: str, backend: str) -> str:
    return sql.replace("?", "%s") if backend == "postgres" else sql


@contextmanager
def push_db() -> Iterable[tuple[Any, str]]:
    backend = _push_db_backend()
    if backend == "postgres":
        if psycopg is None:
            raise RuntimeError("psycopg is required for DATABASE_URL")
        connection = psycopg.connect(PUSH_DATABASE_URL, row_factory=psycopg_dict_row)
    else:
        if not PUSH_SQLITE_PATH:
            raise RuntimeError("Set DATABASE_URL or PUSH_DB_PATH for persistent push subscriptions")
        directory = os.path.dirname(os.path.abspath(PUSH_SQLITE_PATH))
        if directory:
            os.makedirs(directory, exist_ok=True)
        connection = sqlite3.connect(PUSH_SQLITE_PATH, timeout=30)
        connection.row_factory = sqlite3.Row
    try:
        yield connection, backend
        connection.commit()
    except Exception:
        connection.rollback()
        raise
    finally:
        connection.close()


def ensure_push_table() -> None:
    global _PUSH_DB_INITIALIZED
    if _PUSH_DB_INITIALIZED:
        return
    with _PUSH_DB_INIT_LOCK:
        if _PUSH_DB_INITIALIZED:
            return
        with push_db() as (connection, backend):
            connection.execute(_push_sql(
                """
                CREATE TABLE IF NOT EXISTS push_subscriptions (
                    endpoint TEXT PRIMARY KEY,
                    subscription_json TEXT NOT NULL,
                    language TEXT NOT NULL,
                    timezone TEXT NOT NULL,
                    target_url TEXT NOT NULL,
                    next_send_utc TEXT NOT NULL,
                    last_sent_local_date TEXT,
                    failure_count INTEGER NOT NULL DEFAULT 0,
                    active INTEGER NOT NULL DEFAULT 1,
                    claim_token TEXT,
                    claim_until_utc TEXT,
                    created_at TEXT NOT NULL,
                    updated_at TEXT NOT NULL
                )
                """, backend
            ))
            connection.execute(_push_sql(
                "CREATE INDEX IF NOT EXISTS idx_push_due ON push_subscriptions (active, next_send_utc)", backend
            ))
            # Upgrade databases created by an earlier preview of the daily-push
            # feature without dropping any saved browser subscriptions.
            if backend == "postgres":
                column_rows = connection.execute(
                    "SELECT column_name FROM information_schema.columns "
                    "WHERE table_schema = current_schema() AND table_name = 'push_subscriptions'"
                ).fetchall()
                columns = {
                    str(row.get("column_name") if isinstance(row, dict) else row[0])
                    for row in column_rows
                }
            else:
                columns = {str(row[1]) for row in connection.execute("PRAGMA table_info(push_subscriptions)").fetchall()}
            if "claim_token" not in columns:
                connection.execute("ALTER TABLE push_subscriptions ADD COLUMN claim_token TEXT")
            if "claim_until_utc" not in columns:
                connection.execute("ALTER TABLE push_subscriptions ADD COLUMN claim_until_utc TEXT")
        _PUSH_DB_INITIALIZED = True


def _iso_utc(value: datetime) -> str:
    return value.astimezone(UTC).replace(microsecond=0).isoformat()


def _parse_utc(value: str) -> datetime:
    parsed = datetime.fromisoformat(value.replace("Z", "+00:00"))
    return parsed if parsed.tzinfo else parsed.replace(tzinfo=UTC)


def _safe_push_timezone(value: str) -> str:
    try:
        ZoneInfo(value)
        return value
    except (ZoneInfoNotFoundError, ValueError, TypeError):
        return "UTC"


def next_push_time_utc(timezone_name: str, now_utc: datetime | None = None) -> datetime:
    now_value = (now_utc or datetime.now(UTC)).astimezone(UTC)
    zone = ZoneInfo(_safe_push_timezone(timezone_name))
    local_now = now_value.astimezone(zone)
    candidate = datetime(
        local_now.year, local_now.month, local_now.day, PUSH_HOUR_LOCAL, 0, tzinfo=zone
    )
    if candidate <= local_now:
        next_day = local_now.date() + timedelta(days=1)
        candidate = datetime(next_day.year, next_day.month, next_day.day, PUSH_HOUR_LOCAL, 0, tzinfo=zone)
    return candidate.astimezone(UTC)


def _row_dict(row: Any) -> dict[str, Any]:
    return dict(row) if row is not None else {}


def _normalize_push_target(value: Any) -> str:
    target = str(value or "/").strip()
    if len(target) > 2400:
        target = "/"
    parsed = urlsplit(target)
    if parsed.scheme or parsed.netloc or not parsed.path.startswith("/") or parsed.path.startswith("//"):
        return "/"
    if parsed.path.startswith(("/api/", "/sw.js")):
        return "/"
    query = f"?{parsed.query}" if parsed.query else ""
    return f"{parsed.path}{query}"


def _valid_push_subscription(subscription: Any) -> dict[str, Any] | None:
    if not isinstance(subscription, dict):
        return None
    endpoint = str(subscription.get("endpoint") or "").strip()
    keys = subscription.get("keys") if isinstance(subscription.get("keys"), dict) else {}
    auth = str(keys.get("auth") or "").strip()
    p256dh = str(keys.get("p256dh") or "").strip()
    parsed = urlsplit(endpoint)
    if parsed.scheme != "https" or not parsed.hostname or len(endpoint) > 4096:
        return None
    if parsed.hostname.lower() in {"localhost", "127.0.0.1", "::1"}:
        return None
    if not auth or not p256dh or len(auth) > 512 or len(p256dh) > 512:
        return None
    return {"endpoint": endpoint, "expirationTime": subscription.get("expirationTime"), "keys": {"auth": auth, "p256dh": p256dh}}


def upsert_push_subscription(subscription: dict[str, Any], lang: str, timezone_name: str, target_url: str) -> str:
    ensure_push_table()
    now = datetime.now(UTC)
    now_text = _iso_utc(now)
    endpoint = subscription["endpoint"]
    language = lang if lang in LANGUAGES else "en"
    timezone_value = _safe_push_timezone(timezone_name)
    target = _normalize_push_target(target_url)

    existing: dict[str, Any] = {}
    with push_db() as (connection, backend):
        row = connection.execute(
            _push_sql("SELECT timezone, next_send_utc FROM push_subscriptions WHERE endpoint = ?", backend),
            (endpoint,),
        ).fetchone()
        existing = _row_dict(row)
        next_send = next_push_time_utc(timezone_value, now)
        if existing and existing.get("timezone") == timezone_value and existing.get("next_send_utc"):
            try:
                existing_due = _parse_utc(str(existing["next_send_utc"]))
                if existing_due >= now - timedelta(hours=PUSH_DELIVERY_WINDOW_HOURS):
                    next_send = existing_due
            except (TypeError, ValueError):
                pass
        values = (
            endpoint, json.dumps(subscription, separators=(",", ":")), language, timezone_value, target,
            _iso_utc(next_send), None, 0, 1, now_text, now_text,
        )
        sql = """
            INSERT INTO push_subscriptions (
                endpoint, subscription_json, language, timezone, target_url, next_send_utc,
                last_sent_local_date, failure_count, active, created_at, updated_at
            ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            ON CONFLICT(endpoint) DO UPDATE SET
                subscription_json = excluded.subscription_json,
                language = excluded.language,
                timezone = excluded.timezone,
                target_url = excluded.target_url,
                next_send_utc = excluded.next_send_utc,
                active = 1,
                updated_at = excluded.updated_at
        """
        connection.execute(_push_sql(sql, backend), values)
    return _iso_utc(next_send)


def delete_push_subscription(endpoint: str) -> None:
    if not endpoint or not (PUSH_DATABASE_URL or PUSH_SQLITE_PATH):
        return
    ensure_push_table()
    with push_db() as (connection, backend):
        connection.execute(_push_sql("DELETE FROM push_subscriptions WHERE endpoint = ?", backend), (endpoint,))


def _reschedule_push(
    endpoint: str,
    when_utc: datetime,
    failure_count: int | None = None,
    claim_token: str | None = None,
) -> None:
    """Release a delivery claim and move the subscription to another attempt."""
    with push_db() as (connection, backend):
        values: list[Any] = [_iso_utc(when_utc), _iso_utc(datetime.now(UTC))]
        assignments = "next_send_utc = ?, claim_token = NULL, claim_until_utc = NULL, updated_at = ?"
        if failure_count is not None:
            assignments += ", failure_count = ?"
            values.append(failure_count)
        sql = f"UPDATE push_subscriptions SET {assignments} WHERE endpoint = ?"
        values.append(endpoint)
        if claim_token:
            sql += " AND claim_token = ?"
            values.append(claim_token)
        connection.execute(_push_sql(sql, backend), tuple(values))


def _complete_push(
    endpoint: str,
    claim_token: str,
    next_send_utc: datetime,
    local_date: str,
    completed_at: datetime,
) -> None:
    with push_db() as (connection, backend):
        connection.execute(
            _push_sql(
                """
                UPDATE push_subscriptions
                SET next_send_utc = ?, last_sent_local_date = ?, failure_count = 0,
                    claim_token = NULL, claim_until_utc = NULL, updated_at = ?
                WHERE endpoint = ? AND claim_token = ?
                """,
                backend,
            ),
            (_iso_utc(next_send_utc), local_date, _iso_utc(completed_at), endpoint, claim_token),
        )


def claim_due_push_subscriptions(now_utc: datetime | None = None, limit: int = PUSH_MAX_BATCH) -> list[dict[str, Any]]:
    """Lease due rows without marking them delivered.

    A short lease prevents parallel jobs from sending duplicates. If a process
    exits after claiming but before sending, the row becomes eligible again
    after the lease expires instead of silently missing the entire day.
    """
    ensure_push_table()
    now = (now_utc or datetime.now(UTC)).astimezone(UTC)
    now_text = _iso_utc(now)
    cutoff = now - timedelta(hours=PUSH_DELIVERY_WINDOW_HOURS)
    cutoff_text = _iso_utc(cutoff)
    claim_until_text = _iso_utc(now + timedelta(minutes=PUSH_CLAIM_MINUTES))
    claimed: list[dict[str, Any]] = []

    with push_db() as (connection, backend):
        stale_rows = connection.execute(
            _push_sql(
                "SELECT endpoint, timezone, next_send_utc FROM push_subscriptions "
                "WHERE active = 1 AND next_send_utc < ? LIMIT ?",
                backend,
            ),
            (cutoff_text, limit),
        ).fetchall()
        for raw in stale_rows:
            row = _row_dict(raw)
            replacement = _iso_utc(next_push_time_utc(str(row.get("timezone") or "UTC"), now))
            connection.execute(
                _push_sql(
                    """
                    UPDATE push_subscriptions
                    SET next_send_utc = ?, failure_count = 0, claim_token = NULL,
                        claim_until_utc = NULL, updated_at = ?
                    WHERE endpoint = ? AND next_send_utc = ?
                    """,
                    backend,
                ),
                (replacement, now_text, row["endpoint"], row["next_send_utc"]),
            )

        due_rows = connection.execute(
            _push_sql(
                """
                SELECT endpoint, subscription_json, language, timezone, target_url, next_send_utc, failure_count
                FROM push_subscriptions
                WHERE active = 1 AND next_send_utc >= ? AND next_send_utc <= ?
                  AND (claim_until_utc IS NULL OR claim_until_utc <= ?)
                ORDER BY next_send_utc ASC
                LIMIT ?
                """,
                backend,
            ),
            (cutoff_text, now_text, now_text, limit),
        ).fetchall()
        for raw in due_rows:
            row = _row_dict(raw)
            token = secrets.token_urlsafe(18)
            cursor = connection.execute(
                _push_sql(
                    """
                    UPDATE push_subscriptions
                    SET claim_token = ?, claim_until_utc = ?, updated_at = ?
                    WHERE endpoint = ? AND active = 1 AND next_send_utc = ?
                      AND (claim_until_utc IS NULL OR claim_until_utc <= ?)
                    """,
                    backend,
                ),
                (token, claim_until_text, now_text, row["endpoint"], row["next_send_utc"], now_text),
            )
            if cursor.rowcount == 1:
                row["claim_token"] = token
                claimed.append(row)
    return claimed


def _retry_delay_minutes(exc: Exception) -> int:
    retry_after = getattr(exc, "retry_after", None)
    if isinstance(retry_after, (int, float)) and retry_after > 0:
        return max(1, min(180, math.ceil(float(retry_after) / 60)))
    if isinstance(retry_after, str) and retry_after.strip().isdigit():
        return max(1, min(180, math.ceil(int(retry_after.strip()) / 60)))
    return PUSH_RETRY_MINUTES


def send_due_push_notifications(now_utc: datetime | None = None) -> dict[str, int]:
    if not push_feature_enabled():
        raise RuntimeError("Daily push requires DATABASE_URL (or PUSH_DB_PATH), PUSH_SECRET, pywebpush and cryptography")
    now = (now_utc or datetime.now(UTC)).astimezone(UTC)
    vapid = push_vapid_config()
    rows = claim_due_push_subscriptions(now)
    results = {"due": len(rows), "sent": 0, "removed": 0, "retried": 0, "failed": 0}

    for row in rows:
        endpoint = str(row.get("endpoint") or "")
        claim_token = str(row.get("claim_token") or "")
        language = str(row.get("language") or "en")
        timezone_name = _safe_push_timezone(str(row.get("timezone") or "UTC"))
        try:
            subscription = json.loads(str(row["subscription_json"]))
            payload = {
                "title": tr(language, "notification_title"),
                "url": _normalize_push_target(row.get("target_url")),
                "icon": "/icon-512.png",
                "badge": "/badge-96.png",
                "lang": language,
                "timestamp": int(now.timestamp() * 1000),
            }
            webpush(
                subscription_info=subscription,
                data=json.dumps(payload, ensure_ascii=False, separators=(",", ":")),
                vapid_private_key=vapid["private"],
                vapid_claims={"sub": vapid["subject"]},
                ttl=6 * 60 * 60,
                headers={"Urgency": "high", "Topic": "daily-panchang"},
                timeout=12,
            )
            zone = ZoneInfo(timezone_name)
            local_date = now.astimezone(zone).date().isoformat()
            next_send = next_push_time_utc(timezone_name, now + timedelta(seconds=1))
            _complete_push(endpoint, claim_token, next_send, local_date, now)
            results["sent"] += 1
        except WebPushException as exc:
            response = getattr(exc, "response", None)
            status = getattr(exc, "status_code", None) or getattr(response, "status_code", None)
            if status in {404, 410}:
                delete_push_subscription(endpoint)
                results["removed"] += 1
                continue
            failure_count = int(row.get("failure_count") or 0) + 1
            local_now = now.astimezone(ZoneInfo(timezone_name))
            if failure_count <= 3 and local_now.hour < 11:
                _reschedule_push(
                    endpoint,
                    now + timedelta(minutes=_retry_delay_minutes(exc)),
                    failure_count,
                    claim_token,
                )
                results["retried"] += 1
            else:
                _reschedule_push(endpoint, next_push_time_utc(timezone_name, now), failure_count, claim_token)
                results["failed"] += 1
            app.logger.warning("Daily push failed with status %s", status, exc_info=app.debug)
        except Exception:
            failure_count = int(row.get("failure_count") or 0) + 1
            local_now = now.astimezone(ZoneInfo(timezone_name))
            if failure_count <= 3 and local_now.hour < 11:
                _reschedule_push(endpoint, now + timedelta(minutes=PUSH_RETRY_MINUTES), failure_count, claim_token)
                results["retried"] += 1
            else:
                _reschedule_push(endpoint, next_push_time_utc(timezone_name, now), failure_count, claim_token)
                results["failed"] += 1
            app.logger.exception("Daily push failed")
    return results


def validate_push_csrf() -> bool:
    fetch_site = request.headers.get("Sec-Fetch-Site", "")
    if fetch_site and fetch_site not in {"same-origin", "same-site", "none"}:
        return False
    cookie_token = request.cookies.get(PUSH_CSRF_COOKIE, "")
    header_token = request.headers.get("X-Panchang-CSRF", "")
    return bool(cookie_token and header_token and secrets.compare_digest(cookie_token, header_token))


# ---------------------------------------------------------------------------
# Language support
# ---------------------------------------------------------------------------

LANGUAGES: dict[str, dict[str, str]] = {
    "en": {"name": "English", "native": "English", "scheme": ""},
    "hi": {"name": "Hindi", "native": "हिन्दी", "scheme": "devanagari"},
    "mr": {"name": "Marathi", "native": "मराठी", "scheme": "devanagari"},
    "gu": {"name": "Gujarati", "native": "ગુજરાતી", "scheme": "gujarati"},
    "bn": {"name": "Bengali", "native": "বাংলা", "scheme": "bengali"},
    "ta": {"name": "Tamil", "native": "தமிழ்", "scheme": "tamil"},
    "te": {"name": "Telugu", "native": "తెలుగు", "scheme": "telugu"},
    "kn": {"name": "Kannada", "native": "ಕನ್ನಡ", "scheme": "kannada"},
    "ml": {"name": "Malayalam", "native": "മലയാളം", "scheme": "malayalam"},
    "pa": {"name": "Punjabi", "native": "ਪੰਜਾਬੀ", "scheme": "gurmukhi"},
    "or": {"name": "Odia", "native": "ଓଡ଼ିଆ", "scheme": "oriya"},
    "ne": {"name": "Nepali", "native": "नेपाली", "scheme": "devanagari"},
    "sa": {"name": "Sanskrit", "native": "संस्कृतम्", "scheme": "devanagari"},
}

EN_TEXT = {
    "panchang": "Panchang",
    "sunrise": "Sunrise",
    "sunset": "Sunset",
    "tithi": "Tithi",
    "nakshatra": "Nakshatra",
    "yoga": "Yoga",
    "karana": "Karana",
    "choghadiya": "Active Choghadiya",
    "hora": "Active Hora",
    "period": "Current Period",
    "lagna": "Current Lagna",
    "now": "NOW",
    "selected": "SELECTED",
    "today": "TODAY",
    "good": "AUSPICIOUS",
    "avoid": "AVOID",
    "neutral": "NEUTRAL",
    "mixed": "MIXED",
    "live": "LIVE",
    "edit": "Edit Panchang",
    "settings": "Panchang settings",
    "appearance": "Appearance",
    "light_theme": "Light",
    "dark_theme": "Dark",
    "place": "Place",
    "search_place": "Search city, town or postal code",
    "date": "Date",
    "time": "Time",
    "language": "Language",
    "live_time": "Keep date live",
    "use_location": "Use my location",
    "apply": "Show Panchang",
    "cancel": "Cancel",
    "loading": "Calculating your Panchang…",
    "no_results": "No matching places found.",
    "current_location": "Current location",
    "daytime": "Daytime",
    "nighttime": "Nighttime",
    "previous_day": "Previous day",
    "next_day": "Next day",
    "selected_day": "Selected day",
    "location_ready": "Device location selected.",
    "location_denied": "Location permission was not available. Search for a place instead.",
    "place_required": "Choose a place from the search results.",
    "load_error": "Panchang could not be loaded. Please try again.",
    "swipe_hint": "Swipe or horizontally scroll the header for another day.",
    "timeline_hint": "Scroll left for earlier periods and right for upcoming periods.",
    "calculation_note": "Traditional calendrical calculation using Lahiri ayanamsa. Verify important ceremonies with a qualified practitioner.",
    "geocode_attribution": "Place search data: GeoNames via Open-Meteo.",
    "close": "Close",
    "searching": "Searching…",
    "not_available": "Not available",
    "solar_unavailable": "No local sunrise/sunset for this date and latitude",
    "refresh": "Refresh Panchang",
    "refreshing": "Refreshing Panchang…",
    "refreshed": "Panchang refreshed.",
    "auto_refresh": "Automatically refreshes every minute",
    "location_fallback": "Location is unavailable, so Ujjain is being shown.",
    "share_preview": "Social sharing preview",
    "share_preview_help": "This is the image shown when this Panchang link is shared.",
    "share_image_alt": "Panchang social sharing image",
    "upcoming_values": "upcoming values",
    "daily_prompt": "Need Daily Panchang?",
    "yes": "Yes",
    "notification_title": "Today's Panchang",
    "notification_enabled": "Daily Panchang is enabled for 7:00 AM.",
    "notification_blocked": "Notifications are blocked in this browser's settings.",
    "notification_unavailable": "Daily notifications are not supported on this device or browser.",
    "notification_error": "Daily notifications could not be enabled. Please try again.",
    "notification_install_hint": "On iPhone or iPad, add this website to the Home Screen first.",
}

TEXT_OVERRIDES: dict[str, dict[str, str]] = {
    "hi": {
        "panchang": "पंचांग", "sunrise": "सूर्योदय", "sunset": "सूर्यास्त", "tithi": "तिथि",
        "nakshatra": "नक्षत्र", "yoga": "योग", "karana": "करण", "choghadiya": "सक्रिय चौघड़िया",
        "hora": "सक्रिय होरा", "period": "वर्तमान काल", "lagna": "वर्तमान लग्न", "now": "अभी",
        "selected": "चयनित", "today": "आज", "good": "शुभ", "avoid": "अशुभ", "neutral": "सामान्य",
        "mixed": "मिश्रित", "live": "लाइव", "edit": "पंचांग बदलें", "settings": "पंचांग सेटिंग्स",
        "place": "स्थान", "search_place": "शहर, कस्बा या पिन कोड खोजें", "date": "दिनांक", "time": "समय",
        "language": "भाषा", "live_time": "समय को लाइव रखें", "use_location": "मेरा स्थान उपयोग करें",
        "apply": "पंचांग दिखाएँ", "cancel": "रद्द करें", "loading": "पंचांग की गणना हो रही है…",
        "no_results": "कोई स्थान नहीं मिला।", "current_location": "वर्तमान स्थान", "daytime": "दिन का समय",
        "nighttime": "रात्रि का समय", "previous_day": "पिछला दिन", "next_day": "अगला दिन",
        "selected_day": "चयनित दिन", "close": "बंद करें", "searching": "खोज रहे हैं…",
    },
    "mr": {
        "panchang": "पंचांग", "sunrise": "सूर्योदय", "sunset": "सूर्यास्त", "tithi": "तिथी",
        "nakshatra": "नक्षत्र", "yoga": "योग", "karana": "करण", "choghadiya": "सक्रिय चौघडिया",
        "hora": "सक्रिय होरा", "period": "सध्याचा काल", "lagna": "वर्तमान लग्न", "now": "आत्ता",
        "selected": "निवडलेले", "today": "आज", "good": "शुभ", "avoid": "अशुभ", "neutral": "सामान्य",
        "edit": "पंचांग बदला", "place": "ठिकाण", "date": "दिनांक", "time": "वेळ", "language": "भाषा",
        "use_location": "माझे स्थान वापरा", "apply": "पंचांग दाखवा", "cancel": "रद्द करा",
        "current_location": "सध्याचे स्थान", "daytime": "दिवस", "nighttime": "रात्र",
    },
    "gu": {
        "panchang": "પંચાંગ", "sunrise": "સૂર્યોદય", "sunset": "સૂર્યાસ્ત", "tithi": "તિથિ",
        "nakshatra": "નક્ષત્ર", "yoga": "યોગ", "karana": "કરણ", "choghadiya": "સક્રિય ચોઘડિયા",
        "hora": "સક્રિય હોરા", "period": "વર્તમાન કાળ", "lagna": "વર્તમાન લગ્ન", "now": "હમણાં",
        "selected": "પસંદ કરેલ", "today": "આજે", "good": "શુભ", "avoid": "અશુભ", "neutral": "સામાન્ય",
        "edit": "પંચાંગ બદલો", "place": "સ્થળ", "date": "તારીખ", "time": "સમય", "language": "ભાષા",
        "use_location": "મારું સ્થાન વાપરો", "apply": "પંચાંગ બતાવો", "cancel": "રદ કરો",
        "current_location": "વર્તમાન સ્થાન", "daytime": "દિવસ", "nighttime": "રાત",
    },
    "bn": {
        "panchang": "পঞ্জিকা", "sunrise": "সূর্যোদয়", "sunset": "সূর্যাস্ত", "tithi": "তিথি",
        "nakshatra": "নক্ষত্র", "yoga": "যোগ", "karana": "করণ", "choghadiya": "সক্রিয় চৌঘড়িয়া",
        "hora": "সক্রিয় হোরা", "period": "বর্তমান সময়কাল", "lagna": "বর্তমান লগ্ন", "now": "এখন",
        "selected": "নির্বাচিত", "today": "আজ", "good": "শুভ", "avoid": "অশুভ", "neutral": "সাধারণ",
        "edit": "পঞ্জিকা বদলান", "place": "স্থান", "date": "তারিখ", "time": "সময়", "language": "ভাষা",
        "use_location": "আমার অবস্থান ব্যবহার করুন", "apply": "পঞ্জিকা দেখুন", "cancel": "বাতিল",
        "current_location": "বর্তমান অবস্থান", "daytime": "দিন", "nighttime": "রাত",
    },
    "ta": {
        "panchang": "பஞ்சாங்கம்", "sunrise": "சூரிய உதயம்", "sunset": "சூரிய அஸ்தமனம்", "tithi": "திதி",
        "nakshatra": "நட்சத்திரம்", "yoga": "யோகம்", "karana": "கரணம்", "choghadiya": "தற்போதைய சௌகடியா",
        "hora": "தற்போதைய ஹோரை", "period": "தற்போதைய காலம்", "lagna": "தற்போதைய லக்னம்", "now": "இப்போது",
        "selected": "தேர்ந்தெடுத்தது", "today": "இன்று", "good": "சுபம்", "avoid": "தவிர்க்கவும்", "neutral": "சாதாரணம்",
        "edit": "பஞ்சாங்கத்தை மாற்று", "place": "இடம்", "date": "தேதி", "time": "நேரம்", "language": "மொழி",
        "use_location": "என் இருப்பிடத்தைப் பயன்படுத்து", "apply": "பஞ்சாங்கம் காட்டு", "cancel": "ரத்து",
        "current_location": "தற்போதைய இருப்பிடம்", "daytime": "பகல்", "nighttime": "இரவு",
    },
    "te": {
        "panchang": "పంచాంగం", "sunrise": "సూర్యోదయం", "sunset": "సూర్యాస్తమయం", "tithi": "తిథి",
        "nakshatra": "నక్షత్రం", "yoga": "యోగం", "karana": "కరణం", "choghadiya": "ప్రస్తుత చౌఘడియా",
        "hora": "ప్రస్తుత హోరా", "period": "ప్రస్తుత కాలం", "lagna": "ప్రస్తుత లగ్నం", "now": "ఇప్పుడు",
        "selected": "ఎంచుకున్నది", "today": "ఈ రోజు", "good": "శుభం", "avoid": "అశుభం", "neutral": "సాధారణం",
        "edit": "పంచాంగం మార్చండి", "place": "స్థలం", "date": "తేదీ", "time": "సమయం", "language": "భాష",
        "use_location": "నా స్థానాన్ని వాడండి", "apply": "పంచాంగం చూపండి", "cancel": "రద్దు",
        "current_location": "ప్రస్తుత స్థానం", "daytime": "పగలు", "nighttime": "రాత్రి",
    },
    "kn": {
        "panchang": "ಪಂಚಾಂಗ", "sunrise": "ಸೂರ್ಯೋದಯ", "sunset": "ಸೂರ್ಯಾಸ್ತ", "tithi": "ತಿಥಿ",
        "nakshatra": "ನಕ್ಷತ್ರ", "yoga": "ಯೋಗ", "karana": "ಕರಣ", "choghadiya": "ಪ್ರಸ್ತುತ ಚೌಘಡಿಯಾ",
        "hora": "ಪ್ರಸ್ತುತ ಹೋರಾ", "period": "ಪ್ರಸ್ತುತ ಅವಧಿ", "lagna": "ಪ್ರಸ್ತುತ ಲಗ್ನ", "now": "ಈಗ",
        "selected": "ಆಯ್ದ", "today": "ಇಂದು", "good": "ಶುಭ", "avoid": "ಅಶುಭ", "neutral": "ಸಾಮಾನ್ಯ",
        "edit": "ಪಂಚಾಂಗ ಬದಲಿಸಿ", "place": "ಸ್ಥಳ", "date": "ದಿನಾಂಕ", "time": "ಸಮಯ", "language": "ಭಾಷೆ",
        "use_location": "ನನ್ನ ಸ್ಥಳ ಬಳಸಿ", "apply": "ಪಂಚಾಂಗ ತೋರಿಸಿ", "cancel": "ರದ್ದು",
        "current_location": "ಪ್ರಸ್ತುತ ಸ್ಥಳ", "daytime": "ಹಗಲು", "nighttime": "ರಾತ್ರಿ",
    },
    "ml": {
        "panchang": "പഞ്ചാംഗം", "sunrise": "സൂര്യോദയം", "sunset": "സൂര്യാസ്തമയം", "tithi": "തിഥി",
        "nakshatra": "നക്ഷത്രം", "yoga": "യോഗം", "karana": "കരണം", "choghadiya": "നിലവിലെ ചൗഘഡിയ",
        "hora": "നിലവിലെ ഹോര", "period": "നിലവിലെ കാലം", "lagna": "നിലവിലെ ലഗ്നം", "now": "ഇപ്പോൾ",
        "selected": "തിരഞ്ഞെടുത്തത്", "today": "ഇന്ന്", "good": "ശുഭം", "avoid": "അശുഭം", "neutral": "സാധാരണം",
        "edit": "പഞ്ചാംഗം മാറ്റുക", "place": "സ്ഥലം", "date": "തീയതി", "time": "സമയം", "language": "ഭാഷ",
        "use_location": "എന്റെ സ്ഥാനം ഉപയോഗിക്കുക", "apply": "പഞ്ചാംഗം കാണിക്കുക", "cancel": "റദ്ദാക്കുക",
        "current_location": "നിലവിലെ സ്ഥാനം", "daytime": "പകൽ", "nighttime": "രാത്രി",
    },
    "pa": {
        "panchang": "ਪੰਚਾਂਗ", "sunrise": "ਸੂਰਜ ਚੜ੍ਹਨਾ", "sunset": "ਸੂਰਜ ਡੁੱਬਣਾ", "tithi": "ਤਿਥੀ",
        "nakshatra": "ਨਕਸ਼ਤਰ", "yoga": "ਯੋਗ", "karana": "ਕਰਣ", "choghadiya": "ਮੌਜੂਦਾ ਚੌਘੜੀਆ",
        "hora": "ਮੌਜੂਦਾ ਹੋਰਾ", "period": "ਮੌਜੂਦਾ ਸਮਾਂ", "lagna": "ਮੌਜੂਦਾ ਲਗਨ", "now": "ਹੁਣ",
        "selected": "ਚੁਣਿਆ", "today": "ਅੱਜ", "good": "ਸ਼ੁਭ", "avoid": "ਅਸ਼ੁਭ", "neutral": "ਸਧਾਰਨ",
        "edit": "ਪੰਚਾਂਗ ਬਦਲੋ", "place": "ਸਥਾਨ", "date": "ਤਾਰੀਖ", "time": "ਸਮਾਂ", "language": "ਭਾਸ਼ਾ",
        "use_location": "ਮੇਰਾ ਸਥਾਨ ਵਰਤੋ", "apply": "ਪੰਚਾਂਗ ਦਿਖਾਓ", "cancel": "ਰੱਦ ਕਰੋ",
        "current_location": "ਮੌਜੂਦਾ ਸਥਾਨ", "daytime": "ਦਿਨ", "nighttime": "ਰਾਤ",
    },
    "or": {
        "panchang": "ପଞ୍ଚାଙ୍ଗ", "sunrise": "ସୂର୍ଯ୍ୟୋଦୟ", "sunset": "ସୂର୍ଯ୍ୟାସ୍ତ", "tithi": "ତିଥି",
        "nakshatra": "ନକ୍ଷତ୍ର", "yoga": "ଯୋଗ", "karana": "କରଣ", "choghadiya": "ବର୍ତ୍ତମାନ ଚଉଘଡ଼ିଆ",
        "hora": "ବର୍ତ୍ତମାନ ହୋରା", "period": "ବର୍ତ୍ତମାନ କାଳ", "lagna": "ବର୍ତ୍ତମାନ ଲଗ୍ନ", "now": "ଏବେ",
        "selected": "ଚୟନିତ", "today": "ଆଜି", "good": "ଶୁଭ", "avoid": "ଅଶୁଭ", "neutral": "ସାଧାରଣ",
        "edit": "ପଞ୍ଚାଙ୍ଗ ବଦଳାନ୍ତୁ", "place": "ସ୍ଥାନ", "date": "ତାରିଖ", "time": "ସମୟ", "language": "ଭାଷା",
        "use_location": "ମୋ ସ୍ଥାନ ବ୍ୟବହାର କରନ୍ତୁ", "apply": "ପଞ୍ଚାଙ୍ଗ ଦେଖାନ୍ତୁ", "cancel": "ବାତିଲ",
        "current_location": "ବର୍ତ୍ତମାନ ସ୍ଥାନ", "daytime": "ଦିନ", "nighttime": "ରାତି",
    },
    "ne": {
        "panchang": "पञ्चाङ्ग", "sunrise": "सूर्योदय", "sunset": "सूर्यास्त", "tithi": "तिथि",
        "nakshatra": "नक्षत्र", "yoga": "योग", "karana": "करण", "choghadiya": "सक्रिय चौघडिया",
        "hora": "सक्रिय होरा", "period": "वर्तमान अवधि", "lagna": "वर्तमान लग्न", "now": "अहिले",
        "selected": "छानिएको", "today": "आज", "good": "शुभ", "avoid": "अशुभ", "neutral": "सामान्य",
        "edit": "पञ्चाङ्ग बदल्नुहोस्", "place": "स्थान", "date": "मिति", "time": "समय", "language": "भाषा",
        "use_location": "मेरो स्थान प्रयोग गर्नुहोस्", "apply": "पञ्चाङ्ग देखाउनुहोस्", "cancel": "रद्द",
        "current_location": "वर्तमान स्थान", "daytime": "दिन", "nighttime": "रात",
    },
    "sa": {
        "panchang": "पञ्चाङ्गम्", "sunrise": "सूर्योदयः", "sunset": "सूर्यास्तः", "tithi": "तिथिः",
        "nakshatra": "नक्षत्रम्", "yoga": "योगः", "karana": "करणम्", "choghadiya": "वर्तमान-चौघडिया",
        "hora": "वर्तमान-होरा", "period": "वर्तमानकालः", "lagna": "वर्तमानलग्नम्", "now": "इदानीम्",
        "selected": "चितम्", "today": "अद्य", "good": "शुभम्", "avoid": "अशुभम्", "neutral": "सामान्यम्",
        "edit": "पञ्चाङ्गं परिवर्तयतु", "place": "स्थानम्", "date": "दिनाङ्कः", "time": "समयः", "language": "भाषा",
        "use_location": "मम स्थानं प्रयोजयतु", "apply": "पञ्चाङ्गं दर्शयतु", "cancel": "निरस्यतु",
        "current_location": "वर्तमानस्थानम्", "daytime": "दिवा", "nighttime": "रात्रिः",
    },
}

REFRESH_TEXT: dict[str, dict[str, str]] = {
    "hi": {"refresh": "पंचांग ताज़ा करें", "refreshing": "पंचांग ताज़ा हो रहा है…", "refreshed": "पंचांग ताज़ा हो गया।"},
    "mr": {"refresh": "पंचांग रीफ्रेश करा", "refreshing": "पंचांग रीफ्रेश होत आहे…", "refreshed": "पंचांग रीफ्रेश झाले."},
    "gu": {"refresh": "પંચાંગ તાજું કરો", "refreshing": "પંચાંગ તાજું થઈ રહ્યું છે…", "refreshed": "પંચાંગ તાજું થયું."},
    "bn": {"refresh": "পঞ্জিকা রিফ্রেশ করুন", "refreshing": "পঞ্জিকা রিফ্রেশ হচ্ছে…", "refreshed": "পঞ্জিকা রিফ্রেশ হয়েছে।"},
    "ta": {"refresh": "பஞ்சாங்கத்தை புதுப்பிக்கவும்", "refreshing": "பஞ்சாங்கம் புதுப்பிக்கப்படுகிறது…", "refreshed": "பஞ்சாங்கம் புதுப்பிக்கப்பட்டது."},
    "te": {"refresh": "పంచాంగాన్ని రిఫ్రెష్ చేయండి", "refreshing": "పంచాంగం రిఫ్రెష్ అవుతోంది…", "refreshed": "పంచాంగం రిఫ్రెష్ అయింది."},
    "kn": {"refresh": "ಪಂಚಾಂಗವನ್ನು ರಿಫ್ರೆಶ್ ಮಾಡಿ", "refreshing": "ಪಂಚಾಂಗ ರಿಫ್ರೆಶ್ ಆಗುತ್ತಿದೆ…", "refreshed": "ಪಂಚಾಂಗ ರಿಫ್ರೆಶ್ ಆಯಿತು."},
    "ml": {"refresh": "പഞ്ചാംഗം പുതുക്കുക", "refreshing": "പഞ്ചാംഗം പുതുക്കുന്നു…", "refreshed": "പഞ്ചാംഗം പുതുക്കി."},
    "pa": {"refresh": "ਪੰਚਾਂਗ ਤਾਜ਼ਾ ਕਰੋ", "refreshing": "ਪੰਚਾਂਗ ਤਾਜ਼ਾ ਹੋ ਰਿਹਾ ਹੈ…", "refreshed": "ਪੰਚਾਂਗ ਤਾਜ਼ਾ ਹੋ ਗਿਆ।"},
    "or": {"refresh": "ପଞ୍ଚାଙ୍ଗ ସତେଜ କରନ୍ତୁ", "refreshing": "ପଞ୍ଚାଙ୍ଗ ସତେଜ ହେଉଛି…", "refreshed": "ପଞ୍ଚାଙ୍ଗ ସତେଜ ହେଲା।"},
    "ne": {"refresh": "पञ्चाङ्ग रिफ्रेस गर्नुहोस्", "refreshing": "पञ्चाङ्ग रिफ्रेस हुँदैछ…", "refreshed": "पञ्चाङ्ग रिफ्रेस भयो।"},
    "sa": {"refresh": "पञ्चाङ्गं नवीकरोतु", "refreshing": "पञ्चाङ्गं नवीक्रियते…", "refreshed": "पञ्चाङ्गं नवीकृतम्।"},
}
for _language_code, _refresh_values in REFRESH_TEXT.items():
    TEXT_OVERRIDES.setdefault(_language_code, {}).update(_refresh_values)

THEME_TEXT: dict[str, dict[str, str]] = {
    "hi": {"appearance": "दिखावट", "light_theme": "हल्का", "dark_theme": "गहरा"},
    "mr": {"appearance": "स्वरूप", "light_theme": "उजळ", "dark_theme": "गडद"},
    "gu": {"appearance": "દેખાવ", "light_theme": "ઉજળું", "dark_theme": "ગાઢ"},
    "bn": {"appearance": "চেহারা", "light_theme": "হালকা", "dark_theme": "গাঢ়"},
    "ta": {"appearance": "தோற்றம்", "light_theme": "வெளிச்சம்", "dark_theme": "இருள்"},
    "te": {"appearance": "రూపం", "light_theme": "లైట్", "dark_theme": "డార్క్"},
    "kn": {"appearance": "ರೂಪ", "light_theme": "ಬೆಳಕು", "dark_theme": "ಗಾಢ"},
    "ml": {"appearance": "രൂപഭാവം", "light_theme": "വെളിച്ചം", "dark_theme": "ഇരുണ്ട"},
    "pa": {"appearance": "ਦਿੱਖ", "light_theme": "ਹਲਕਾ", "dark_theme": "ਗੂੜ੍ਹਾ"},
    "or": {"appearance": "ଦେଖାଶୁଣା", "light_theme": "ଉଜ୍ଜ୍ୱଳ", "dark_theme": "ଗାଢ଼"},
    "ne": {"appearance": "रूप", "light_theme": "उज्यालो", "dark_theme": "गाढा"},
    "sa": {"appearance": "रूपम्", "light_theme": "प्रकाशः", "dark_theme": "अन्धकारः"},
}
for _language_code, _theme_values in THEME_TEXT.items():
    TEXT_OVERRIDES.setdefault(_language_code, {}).update(_theme_values)

LIVE_MODE_TEXT: dict[str, str] = {
    "hi": "दिनांक लाइव रखें",
    "mr": "दिनांक लाइव्ह ठेवा",
    "gu": "તારીખ લાઇવ રાખો",
    "bn": "তারিখ লাইভ রাখুন",
    "ta": "தேதியை நேரலையில் வைத்திரு",
    "te": "తేదీని లైవ్‌గా ఉంచండి",
    "kn": "ದಿನಾಂಕವನ್ನು ಲೈವ್ ಇರಿಸಿ",
    "ml": "തീയതി തത്സമയം നിലനിർത്തുക",
    "pa": "ਤਾਰੀਖ ਲਾਈਵ ਰੱਖੋ",
    "or": "ତାରିଖକୁ ଲାଇଭ୍ ରଖନ୍ତୁ",
    "ne": "मिति लाइभ राख्नुहोस्",
    "sa": "दिनाङ्कं सजीवं स्थापयतु",
}
for _language_code, _live_label in LIVE_MODE_TEXT.items():
    TEXT_OVERRIDES.setdefault(_language_code, {})["live_time"] = _live_label


SHARE_TEXT: dict[str, dict[str, str]] = {
    "hi": {
        "share_preview": "सोशल शेयर पूर्वावलोकन", "share_preview_help": "पंचांग लिंक साझा करने पर यही चित्र दिखाई देगा।",
        "share_image_alt": "पंचांग साझा चित्र", "upcoming_values": "आगामी मान",
    },
    "mr": {
        "share_preview": "सोशल शेअर पूर्वदृश्य", "share_preview_help": "पंचांगाची लिंक शेअर केल्यावर ही प्रतिमा दिसेल.",
        "share_image_alt": "पंचांग शेअर प्रतिमा", "upcoming_values": "पुढील मूल्ये", "mixed": "मिश्र", "live": "थेट",
    },
    "gu": {
        "share_preview": "સોશિયલ શેર પૂર્વદર્શન", "share_preview_help": "પંચાંગની લિંક શેર કરતાં આ ચિત્ર દેખાશે.",
        "share_image_alt": "પંચાંગ શેર ચિત્ર", "upcoming_values": "આગામી મૂલ્યો", "mixed": "મિશ્ર", "live": "લાઇવ",
    },
    "bn": {
        "share_preview": "সামাজিক শেয়ার পূর্বরূপ", "share_preview_help": "পঞ্জিকার লিঙ্ক শেয়ার করলে এই ছবিটি দেখা যাবে।",
        "share_image_alt": "পঞ্জিকা শেয়ার ছবি", "upcoming_values": "আসন্ন মান", "mixed": "মিশ্র", "live": "লাইভ",
    },
    "ta": {
        "share_preview": "சமூக பகிர்வு முன்னோட்டம்", "share_preview_help": "பஞ்சாங்க இணைப்பைப் பகிரும்போது இந்தப் படம் தோன்றும்.",
        "share_image_alt": "பஞ்சாங்க பகிர்வு படம்", "upcoming_values": "வரவிருக்கும் மதிப்புகள்", "mixed": "கலப்பு", "live": "நேரலை",
    },
    "te": {
        "share_preview": "సామాజిక భాగస్వామ్య ముందస్తు చిత్రం", "share_preview_help": "పంచాంగం లింక్‌ను పంచుకున్నప్పుడు ఈ చిత్రం కనిపిస్తుంది.",
        "share_image_alt": "పంచాంగం భాగస్వామ్య చిత్రం", "upcoming_values": "రాబోయే విలువలు", "mixed": "మిశ్రమం", "live": "లైవ్",
    },
    "kn": {
        "share_preview": "ಸಾಮಾಜಿಕ ಹಂಚಿಕೆ ಮುನ್ನೋಟ", "share_preview_help": "ಪಂಚಾಂಗದ ಕೊಂಡಿಯನ್ನು ಹಂಚಿದಾಗ ಈ ಚಿತ್ರ ಕಾಣಿಸುತ್ತದೆ.",
        "share_image_alt": "ಪಂಚಾಂಗ ಹಂಚಿಕೆ ಚಿತ್ರ", "upcoming_values": "ಮುಂದಿನ ಮೌಲ್ಯಗಳು", "mixed": "ಮಿಶ್ರ", "live": "ಲೈವ್",
    },
    "ml": {
        "share_preview": "സാമൂഹിക പങ്കിടൽ പ്രിവ്യൂ", "share_preview_help": "പഞ്ചാംഗ ലിങ്ക് പങ്കിടുമ്പോൾ ഈ ചിത്രം കാണിക്കും.",
        "share_image_alt": "പഞ്ചാംഗ പങ്കിടൽ ചിത്രം", "upcoming_values": "വരാനിരിക്കുന്ന മൂല്യങ്ങൾ", "mixed": "മിശ്രം", "live": "ലൈവ്",
    },
    "pa": {
        "share_preview": "ਸਮਾਜਿਕ ਸਾਂਝ ਪੂਰਵ-ਝਲਕ", "share_preview_help": "ਪੰਚਾਂਗ ਲਿੰਕ ਸਾਂਝਾ ਕਰਨ ਵੇਲੇ ਇਹ ਤਸਵੀਰ ਦਿਖਾਈ ਦੇਵੇਗੀ।",
        "share_image_alt": "ਪੰਚਾਂਗ ਸਾਂਝੀ ਤਸਵੀਰ", "upcoming_values": "ਆਉਣ ਵਾਲੇ ਮੁੱਲ", "mixed": "ਮਿਸ਼ਰਤ", "live": "ਲਾਈਵ",
    },
    "or": {
        "share_preview": "ସାମାଜିକ ଅଂଶୀଦାର ପୂର୍ବଦୃଶ୍ୟ", "share_preview_help": "ପଞ୍ଚାଙ୍ଗ ଲିଙ୍କ ଅଂଶୀଦାର କଲେ ଏହି ଛବି ଦେଖାଯିବ।",
        "share_image_alt": "ପଞ୍ଚାଙ୍ଗ ଅଂଶୀଦାର ଛବି", "upcoming_values": "ଆଗାମୀ ମୂଲ୍ୟ", "mixed": "ମିଶ୍ର", "live": "ଲାଇଭ୍",
    },
    "ne": {
        "share_preview": "सामाजिक साझेदारी पूर्वावलोकन", "share_preview_help": "पञ्चाङ्गको लिङ्क साझा गर्दा यही चित्र देखिन्छ।",
        "share_image_alt": "पञ्चाङ्ग साझा चित्र", "upcoming_values": "आगामी मान", "mixed": "मिश्रित", "live": "लाइभ",
    },
    "sa": {
        "share_preview": "सामाजिक-वितरण-पूर्वदृश्यम्", "share_preview_help": "पञ्चाङ्गस्य सम्बन्धकं वितरति चेत् इदं चित्रं दृश्यते।",
        "share_image_alt": "पञ्चाङ्ग-वितरण-चित्रम्", "upcoming_values": "आगामिमूल्यानि", "mixed": "मिश्रम्", "live": "सजीवम्",
    },
}
for _language_code, _share_values in SHARE_TEXT.items():
    TEXT_OVERRIDES.setdefault(_language_code, {}).update(_share_values)

PUSH_TEXT: dict[str, dict[str, str]] = {
    "hi": {
        "daily_prompt": "दैनिक पंचांग चाहिए?", "yes": "हाँ", "notification_title": "आज का पंचांग",
        "notification_enabled": "प्रतिदिन सुबह 7:00 बजे पंचांग सूचना चालू है।",
        "notification_blocked": "इस ब्राउज़र की सेटिंग में सूचनाएँ बंद हैं।",
        "notification_unavailable": "इस डिवाइस या ब्राउज़र में दैनिक सूचनाएँ उपलब्ध नहीं हैं।",
        "notification_error": "दैनिक सूचनाएँ चालू नहीं हो सकीं। कृपया फिर प्रयास करें।",
        "notification_install_hint": "iPhone या iPad पर पहले इस वेबसाइट को होम स्क्रीन पर जोड़ें।",
    },
    "mr": {
        "daily_prompt": "रोजचे पंचांग हवे?", "yes": "हो", "notification_title": "आजचे पंचांग",
        "notification_enabled": "दररोज सकाळी 7:00 वाजताची पंचांग सूचना सुरू आहे।",
        "notification_blocked": "या ब्राउझरच्या सेटिंगमध्ये सूचना बंद आहेत।",
        "notification_unavailable": "या डिव्हाइस किंवा ब्राउझरवर दैनिक सूचना उपलब्ध नाहीत।",
        "notification_error": "दैनिक सूचना सुरू करता आल्या नाहीत. पुन्हा प्रयत्न करा।",
        "notification_install_hint": "iPhone किंवा iPad वर आधी ही वेबसाइट होम स्क्रीनवर जोडा।",
    },
    "gu": {
        "daily_prompt": "દૈનિક પંચાંગ જોઈએ?", "yes": "હા", "notification_title": "આજનું પંચાંગ",
        "notification_enabled": "દરરોજ સવારે 7:00 વાગ્યાની પંચાંગ સૂચના ચાલુ છે.",
        "notification_blocked": "આ બ્રાઉઝરની સેટિંગમાં સૂચનાઓ બંધ છે.",
        "notification_unavailable": "આ ઉપકરણ અથવા બ્રાઉઝરમાં દૈનિક સૂચનાઓ ઉપલબ્ધ નથી.",
        "notification_error": "દૈનિક સૂચનાઓ ચાલુ થઈ શકી નથી. ફરી પ્રયત્ન કરો.",
        "notification_install_hint": "iPhone અથવા iPad પર પહેલાં આ વેબસાઇટને હોમ સ્ક્રીન પર ઉમેરો.",
    },
    "bn": {
        "daily_prompt": "দৈনিক পঞ্জিকা চান?", "yes": "হ্যাঁ", "notification_title": "আজকের পঞ্জিকা",
        "notification_enabled": "প্রতিদিন সকাল ৭:০০টার পঞ্জিকা বিজ্ঞপ্তি চালু হয়েছে।",
        "notification_blocked": "এই ব্রাউজারের সেটিংসে বিজ্ঞপ্তি বন্ধ রয়েছে।",
        "notification_unavailable": "এই ডিভাইস বা ব্রাউজারে দৈনিক বিজ্ঞপ্তি সমর্থিত নয়।",
        "notification_error": "দৈনিক বিজ্ঞপ্তি চালু করা যায়নি। আবার চেষ্টা করুন।",
        "notification_install_hint": "iPhone বা iPad-এ আগে ওয়েবসাইটটি হোম স্ক্রিনে যোগ করুন।",
    },
    "ta": {
        "daily_prompt": "தினசரி பஞ்சாங்கம் வேண்டுமா?", "yes": "ஆம்", "notification_title": "இன்றைய பஞ்சாங்கம்",
        "notification_enabled": "தினமும் காலை 7:00 மணிக்கான பஞ்சாங்க அறிவிப்பு இயக்கப்பட்டது.",
        "notification_blocked": "இந்த உலாவியின் அமைப்புகளில் அறிவிப்புகள் தடுக்கப்பட்டுள்ளன.",
        "notification_unavailable": "இந்த சாதனம் அல்லது உலாவியில் தினசரி அறிவிப்புகள் ஆதரிக்கப்படவில்லை.",
        "notification_error": "தினசரி அறிவிப்புகளை இயக்க முடியவில்லை. மீண்டும் முயலவும்.",
        "notification_install_hint": "iPhone அல்லது iPad-ல் முதலில் இந்த இணையதளத்தை முகப்புத் திரையில் சேர்க்கவும்.",
    },
    "te": {
        "daily_prompt": "రోజువారీ పంచాంగం కావాలా?", "yes": "అవును", "notification_title": "నేటి పంచాంగం",
        "notification_enabled": "ప్రతిరోజూ ఉదయం 7:00 గంటల పంచాంగ నోటిఫికేషన్ ప్రారంభమైంది.",
        "notification_blocked": "ఈ బ్రౌజర్ సెట్టింగుల్లో నోటిఫికేషన్లు నిరోధించబడ్డాయి.",
        "notification_unavailable": "ఈ పరికరం లేదా బ్రౌజర్‌లో రోజువారీ నోటిఫికేషన్లు అందుబాటులో లేవు.",
        "notification_error": "రోజువారీ నోటిఫికేషన్లు ప్రారంభించలేకపోయాము. మళ్లీ ప్రయత్నించండి.",
        "notification_install_hint": "iPhone లేదా iPadలో ముందుగా ఈ వెబ్‌సైట్‌ను హోమ్ స్క్రీన్‌కు జోడించండి.",
    },
    "kn": {
        "daily_prompt": "ದೈನಂದಿನ ಪಂಚಾಂಗ ಬೇಕೇ?", "yes": "ಹೌದು", "notification_title": "ಇಂದಿನ ಪಂಚಾಂಗ",
        "notification_enabled": "ಪ್ರತಿದಿನ ಬೆಳಿಗ್ಗೆ 7:00 ಗಂಟೆಯ ಪಂಚಾಂಗ ಸೂಚನೆ ಸಕ್ರಿಯವಾಗಿದೆ.",
        "notification_blocked": "ಈ ಬ್ರೌಸರ್ ಸೆಟ್ಟಿಂಗ್‌ಗಳಲ್ಲಿ ಸೂಚನೆಗಳನ್ನು ನಿರ್ಬಂಧಿಸಲಾಗಿದೆ.",
        "notification_unavailable": "ಈ ಸಾಧನ ಅಥವಾ ಬ್ರೌಸರ್‌ನಲ್ಲಿ ದೈನಂದಿನ ಸೂಚನೆಗಳು ಲಭ್ಯವಿಲ್ಲ.",
        "notification_error": "ದೈನಂದಿನ ಸೂಚನೆಗಳನ್ನು ಸಕ್ರಿಯಗೊಳಿಸಲು ಸಾಧ್ಯವಾಗಲಿಲ್ಲ. ಮತ್ತೆ ಪ್ರಯತ್ನಿಸಿ.",
        "notification_install_hint": "iPhone ಅಥವಾ iPadನಲ್ಲಿ ಮೊದಲು ಈ ವೆಬ್‌ಸೈಟ್ ಅನ್ನು ಹೋಮ್ ಸ್ಕ್ರೀನ್‌ಗೆ ಸೇರಿಸಿ.",
    },
    "ml": {
        "daily_prompt": "ദിവസേന പഞ്ചാംഗം വേണമോ?", "yes": "അതെ", "notification_title": "ഇന്നത്തെ പഞ്ചാംഗം",
        "notification_enabled": "ദിവസേന രാവിലെ 7:00 മണിക്കുള്ള പഞ്ചാംഗ അറിയിപ്പ് സജീവമാണ്.",
        "notification_blocked": "ഈ ബ്രൗസറിന്റെ ക്രമീകരണങ്ങളിൽ അറിയിപ്പുകൾ തടഞ്ഞിരിക്കുന്നു.",
        "notification_unavailable": "ഈ ഉപകരണത്തിലോ ബ്രൗസറിലോ ദിവസേന അറിയിപ്പുകൾ ലഭ്യമല്ല.",
        "notification_error": "ദിവസേന അറിയിപ്പുകൾ സജീവമാക്കാനായില്ല. വീണ്ടും ശ്രമിക്കുക.",
        "notification_install_hint": "iPhone അല്ലെങ്കിൽ iPadൽ ആദ്യം ഈ വെബ്സൈറ്റ് ഹോം സ്ക്രീനിൽ ചേർക്കുക.",
    },
    "pa": {
        "daily_prompt": "ਰੋਜ਼ਾਨਾ ਪੰਚਾਂਗ ਚਾਹੀਦਾ ਹੈ?", "yes": "ਹਾਂ", "notification_title": "ਅੱਜ ਦਾ ਪੰਚਾਂਗ",
        "notification_enabled": "ਰੋਜ਼ ਸਵੇਰੇ 7:00 ਵਜੇ ਦੀ ਪੰਚਾਂਗ ਸੂਚਨਾ ਚਾਲੂ ਹੈ।",
        "notification_blocked": "ਇਸ ਬ੍ਰਾਊਜ਼ਰ ਦੀਆਂ ਸੈਟਿੰਗਾਂ ਵਿੱਚ ਸੂਚਨਾਵਾਂ ਬੰਦ ਹਨ।",
        "notification_unavailable": "ਇਸ ਡਿਵਾਈਸ ਜਾਂ ਬ੍ਰਾਊਜ਼ਰ ਵਿੱਚ ਰੋਜ਼ਾਨਾ ਸੂਚਨਾਵਾਂ ਉਪਲਬਧ ਨਹੀਂ ਹਨ।",
        "notification_error": "ਰੋਜ਼ਾਨਾ ਸੂਚਨਾਵਾਂ ਚਾਲੂ ਨਹੀਂ ਹੋ ਸਕੀਆਂ। ਦੁਬਾਰਾ ਕੋਸ਼ਿਸ਼ ਕਰੋ।",
        "notification_install_hint": "iPhone ਜਾਂ iPad ਉੱਤੇ ਪਹਿਲਾਂ ਇਸ ਵੈੱਬਸਾਈਟ ਨੂੰ ਹੋਮ ਸਕ੍ਰੀਨ ਵਿੱਚ ਜੋੜੋ।",
    },
    "or": {
        "daily_prompt": "ଦୈନିକ ପଞ୍ଚାଙ୍ଗ ଚାହୁଁଛନ୍ତି କି?", "yes": "ହଁ", "notification_title": "ଆଜିର ପଞ୍ଚାଙ୍ଗ",
        "notification_enabled": "ପ୍ରତିଦିନ ସକାଳ 7:00ଟାର ପଞ୍ଚାଙ୍ଗ ସୂଚନା ସକ୍ରିୟ ହୋଇଛି।",
        "notification_blocked": "ଏହି ବ୍ରାଉଜର ସେଟିଂସ୍‌ରେ ସୂଚନା ବନ୍ଦ ଅଛି।",
        "notification_unavailable": "ଏହି ଡିଭାଇସ୍ କିମ୍ବା ବ୍ରାଉଜରରେ ଦୈନିକ ସୂଚନା ଉପଲବ୍ଧ ନୁହେଁ।",
        "notification_error": "ଦୈନିକ ସୂଚନା ସକ୍ରିୟ କରିହେଲା ନାହିଁ। ପୁଣି ଚେଷ୍ଟା କରନ୍ତୁ।",
        "notification_install_hint": "iPhone କିମ୍ବା iPadରେ ପ୍ରଥମେ ଏହି ୱେବସାଇଟକୁ ହୋମ୍ ସ୍କ୍ରିନ୍‌ରେ ଯୋଡନ୍ତୁ।",
    },
    "ne": {
        "daily_prompt": "दैनिक पञ्चाङ्ग चाहिन्छ?", "yes": "हो", "notification_title": "आजको पञ्चाङ्ग",
        "notification_enabled": "हरेक दिन बिहान ७:०० बजेको पञ्चाङ्ग सूचना सक्रिय छ।",
        "notification_blocked": "यस ब्राउजरको सेटिङमा सूचनाहरू रोकिएका छन्।",
        "notification_unavailable": "यस उपकरण वा ब्राउजरमा दैनिक सूचनाहरू उपलब्ध छैनन्।",
        "notification_error": "दैनिक सूचनाहरू सक्रिय गर्न सकिएन। फेरि प्रयास गर्नुहोस्।",
        "notification_install_hint": "iPhone वा iPad मा पहिले यो वेबसाइट होम स्क्रिनमा थप्नुहोस्।",
    },
    "sa": {
        "daily_prompt": "दैनिकं पञ्चाङ्गम् इच्छति किम्?", "yes": "आम्", "notification_title": "अद्य पञ्चाङ्गम्",
        "notification_enabled": "प्रतिदिनं प्रातः ७:०० वादने पञ्चाङ्गसूचना सक्रियाऽस्ति।",
        "notification_blocked": "अस्य जालदर्शकस्य विन्यासेषु सूचनाः निरुद्धाः सन्ति।",
        "notification_unavailable": "अस्मिन् उपकरणे वा जालदर्शके दैनिकसूचनाः न समर्थिताः।",
        "notification_error": "दैनिकसूचनाः सक्रियाः कर्तुं न शक्यन्ते। पुनः प्रयतताम्।",
        "notification_install_hint": "iPhone अथवा iPad मध्ये प्रथमम् एतत् जालस्थानं मुख्यपटले योजयतु।",
    },
}
for _language_code, _push_values in PUSH_TEXT.items():
    TEXT_OVERRIDES.setdefault(_language_code, {}).update(_push_values)


def ui_text(lang: str) -> dict[str, str]:
    result = dict(EN_TEXT)
    result.update(TEXT_OVERRIDES.get(lang, {}))
    return result


def tr(lang: str, key: str) -> str:
    return ui_text(lang).get(key, EN_TEXT.get(key, key))


# ---------------------------------------------------------------------------
# Sanskrit names and transliteration
# ---------------------------------------------------------------------------

TITHI_NAMES = [
    ("Pratipadā", "Pratipada"), ("Dvitīyā", "Dwitiya"), ("Tṛtīyā", "Tritiya"),
    ("Caturthī", "Chaturthi"), ("Pañcamī", "Panchami"), ("Ṣaṣṭhī", "Shashthi"),
    ("Saptamī", "Saptami"), ("Aṣṭamī", "Ashtami"), ("Navamī", "Navami"),
    ("Daśamī", "Dashami"), ("Ekādaśī", "Ekadashi"), ("Dvādaśī", "Dwadashi"),
    ("Trayodaśī", "Trayodashi"), ("Caturdaśī", "Chaturdashi"), ("Pūrṇimā", "Purnima"),
]
NAKSHATRA_NAMES = [
    ("Aśvinī", "Ashwini"), ("Bharaṇī", "Bharani"), ("Kṛttikā", "Krittika"),
    ("Rohiṇī", "Rohini"), ("Mṛgaśīrṣa", "Mrigashirsha"), ("Ārdrā", "Ardra"),
    ("Punarvasu", "Punarvasu"), ("Puṣya", "Pushya"), ("Āśleṣā", "Ashlesha"),
    ("Maghā", "Magha"), ("Pūrva Phālgunī", "Purva Phalguni"), ("Uttara Phālgunī", "Uttara Phalguni"),
    ("Hasta", "Hasta"), ("Citrā", "Chitra"), ("Svātī", "Swati"),
    ("Viśākhā", "Vishakha"), ("Anurādhā", "Anuradha"), ("Jyeṣṭhā", "Jyeshtha"),
    ("Mūla", "Mula"), ("Pūrva Āṣāḍhā", "Purva Ashadha"), ("Uttara Āṣāḍhā", "Uttara Ashadha"),
    ("Śravaṇa", "Shravana"), ("Dhaniṣṭhā", "Dhanishtha"), ("Śatabhiṣā", "Shatabhisha"),
    ("Pūrva Bhādrapadā", "Purva Bhadrapada"), ("Uttara Bhādrapadā", "Uttara Bhadrapada"),
    ("Revatī", "Revati"),
]
YOGA_NAMES = [
    ("Viṣkambha", "Vishkambha"), ("Prīti", "Priti"), ("Āyuṣmān", "Ayushman"),
    ("Saubhāgya", "Saubhagya"), ("Śobhana", "Shobhana"), ("Atigaṇḍa", "Atiganda"),
    ("Sukarmā", "Sukarma"), ("Dhṛti", "Dhriti"), ("Śūla", "Shula"),
    ("Gaṇḍa", "Ganda"), ("Vṛddhi", "Vriddhi"), ("Dhruva", "Dhruva"),
    ("Vyāghāta", "Vyaghata"), ("Harṣaṇa", "Harshana"), ("Vajra", "Vajra"),
    ("Siddhi", "Siddhi"), ("Vyatīpāta", "Vyatipata"), ("Varīyān", "Variyana"),
    ("Parigha", "Parigha"), ("Śiva", "Shiva"), ("Siddha", "Siddha"),
    ("Sādhya", "Sadhya"), ("Śubha", "Shubha"), ("Śukla", "Shukla"),
    ("Brahma", "Brahma"), ("Indra", "Indra"), ("Vaidhṛti", "Vaidhriti"),
]
KARANA_NAMES = {
    "kimstughna": ("Kiṃstughna", "Kimstughna"), "bava": ("Bava", "Bava"),
    "balava": ("Bālava", "Balava"), "kaulava": ("Kaulava", "Kaulava"),
    "taitila": ("Taitila", "Taitila"), "garaja": ("Garaja", "Garaja"),
    "vanija": ("Vaṇija", "Vanija"), "vishti": ("Viṣṭi", "Vishti (Bhadra)"),
    "shakuni": ("Śakuni", "Shakuni"), "chatushpada": ("Catuṣpada", "Chatushpada"),
    "nagava": ("Nāgava", "Nagava"),
}
RASHI_NAMES = [
    ("Meṣa", "Mesha"), ("Vṛṣabha", "Vrishabha"), ("Mithuna", "Mithuna"),
    ("Karka", "Karka"), ("Siṃha", "Simha"), ("Kanyā", "Kanya"),
    ("Tulā", "Tula"), ("Vṛścika", "Vrishchika"), ("Dhanu", "Dhanu"),
    ("Makara", "Makara"), ("Kumbha", "Kumbha"), ("Mīna", "Meena"),
]
PLANET_NAMES = {
    "sun": ("Sūrya", "Sun"), "moon": ("Candra", "Moon"), "mars": ("Maṅgala", "Mars"),
    "mercury": ("Budha", "Mercury"), "jupiter": ("Guru", "Jupiter"),
    "venus": ("Śukra", "Venus"), "saturn": ("Śani", "Saturn"),
}
CHOGHADIYA_NAMES = {
    "udveg": ("Udvega", "Udveg"), "chal": ("Cara", "Chal"), "labh": ("Lābha", "Labh"),
    "amrit": ("Amṛta", "Amrit"), "kaal": ("Kāla", "Kaal"),
    "shubh": ("Śubha", "Shubh"), "rog": ("Roga", "Rog"),
}
PERIOD_NAMES = {
    "brahma": ("Brahma Muhūrta", "Brahma Muhurta"),
    "pratah": ("Prātaḥ Sandhyā", "Pratah Sandhya"),
    "abhijit": ("Abhijit Muhūrta", "Abhijit Muhurta"),
    "vijaya": ("Vijaya Muhūrta", "Vijaya Muhurta"),
    "rahu": ("Rāhu Kāla", "Rahu Kalam"),
    "yamaganda": ("Yamagaṇḍa Kāla", "Yamaganda"),
    "gulika": ("Gulika Kāla", "Gulika Kalam"),
    "godhuli": ("Godhūli Muhūrta", "Godhuli Muhurta"),
    "sayahna": ("Sāyaṃ Sandhyā", "Sayahna Sandhya"),
    "nishita": ("Niśītha Muhūrta", "Nishita Muhurta"),
    "daytime": ("Divā Kāla", "Daytime"),
    "nighttime": ("Rātri Kāla", "Nighttime"),
}
PAKSHA_NAMES = {
    "shukla": ("Śukla Pakṣa", "Shukla Paksha"),
    "krishna": ("Kṛṣṇa Pakṣa", "Krishna Paksha"),
}


def localize_sanskrit(pair: tuple[str, str], lang: str) -> str:
    """Return a proper name in the selected Indic script, with safe fallback."""
    iast, english_name = pair
    if lang == "en" or lang not in LANGUAGES or not transliterate or not sanscript:
        return english_name
    scheme_name = LANGUAGES[lang].get("scheme", "")
    if not scheme_name:
        return english_name
    try:
        return transliterate(iast, sanscript.IAST, scheme_name)
    except Exception:
        return english_name


def join_localized(parts: Iterable[tuple[str, str] | str], lang: str, separator: str = " ") -> str:
    out: list[str] = []
    for part in parts:
        out.append(localize_sanskrit(part, lang) if isinstance(part, tuple) else str(part))
    return separator.join(out)


# ---------------------------------------------------------------------------
# Place catalogue and request parsing
# ---------------------------------------------------------------------------

POPULAR_PLACES: dict[str, dict[str, Any]] = {
    "ujjain": {**DEFAULT_PLACE},
    "new-delhi": {"name": "New Delhi", "latitude": 28.6139, "longitude": 77.2090, "timezone": "Asia/Kolkata", "country": "India"},
    "mumbai": {"name": "Mumbai", "latitude": 19.0760, "longitude": 72.8777, "timezone": "Asia/Kolkata", "country": "India"},
    "bengaluru": {"name": "Bengaluru", "latitude": 12.9716, "longitude": 77.5946, "timezone": "Asia/Kolkata", "country": "India"},
    "chennai": {"name": "Chennai", "latitude": 13.0827, "longitude": 80.2707, "timezone": "Asia/Kolkata", "country": "India"},
    "kolkata": {"name": "Kolkata", "latitude": 22.5726, "longitude": 88.3639, "timezone": "Asia/Kolkata", "country": "India"},
    "hyderabad": {"name": "Hyderabad", "latitude": 17.3850, "longitude": 78.4867, "timezone": "Asia/Kolkata", "country": "India"},
    "ahmedabad": {"name": "Ahmedabad", "latitude": 23.0225, "longitude": 72.5714, "timezone": "Asia/Kolkata", "country": "India"},
    "pune": {"name": "Pune", "latitude": 18.5204, "longitude": 73.8567, "timezone": "Asia/Kolkata", "country": "India"},
    "jaipur": {"name": "Jaipur", "latitude": 26.9124, "longitude": 75.7873, "timezone": "Asia/Kolkata", "country": "India"},
    "varanasi": {"name": "Varanasi", "latitude": 25.3176, "longitude": 82.9739, "timezone": "Asia/Kolkata", "country": "India"},
    "kathmandu": {"name": "Kathmandu", "latitude": 27.7172, "longitude": 85.3240, "timezone": "Asia/Kathmandu", "country": "Nepal"},
    "dubai": {"name": "Dubai", "latitude": 25.2048, "longitude": 55.2708, "timezone": "Asia/Dubai", "country": "United Arab Emirates"},
    "singapore": {"name": "Singapore", "latitude": 1.3521, "longitude": 103.8198, "timezone": "Asia/Singapore", "country": "Singapore"},
    "london": {"name": "London", "latitude": 51.5072, "longitude": -0.1276, "timezone": "Europe/London", "country": "United Kingdom"},
    "new-york": {"name": "New York", "latitude": 40.7128, "longitude": -74.0060, "timezone": "America/New_York", "country": "United States"},
    "toronto": {"name": "Toronto", "latitude": 43.6532, "longitude": -79.3832, "timezone": "America/Toronto", "country": "Canada"},
    "los-angeles": {"name": "Los Angeles", "latitude": 34.0522, "longitude": -118.2437, "timezone": "America/Los_Angeles", "country": "United States"},
    "sydney": {"name": "Sydney", "latitude": -33.8688, "longitude": 151.2093, "timezone": "Australia/Sydney", "country": "Australia"},
}


def clamp_float(raw: str | None, default: float, lower: float, upper: float) -> float:
    try:
        value = float(raw) if raw is not None else default
        if not math.isfinite(value):
            return default
        return max(lower, min(upper, value))
    except (TypeError, ValueError):
        return default


def safe_timezone(raw: str | None, fallback: str = "Asia/Kolkata") -> tuple[str, ZoneInfo]:
    candidate = (raw or fallback).strip()[:80]
    try:
        return candidate, ZoneInfo(candidate)
    except (ZoneInfoNotFoundError, ValueError):
        return fallback, ZoneInfo(fallback)


def safe_date(raw: str | None, fallback: date) -> date:
    try:
        parsed = date.fromisoformat(raw or "")
        if 1600 <= parsed.year <= 2400:
            return parsed
    except ValueError:
        pass
    return fallback


def safe_time(raw: str | None, fallback: dt_time) -> dt_time:
    try:
        cleaned = (raw or "").strip()
        if re.fullmatch(r"\d{2}:\d{2}", cleaned):
            return dt_time.fromisoformat(cleaned)
        if re.fullmatch(r"\d{2}:\d{2}:\d{2}", cleaned):
            return dt_time.fromisoformat(cleaned)
    except ValueError:
        pass
    return fallback.replace(second=0, microsecond=0)


def slugify_place(value: str) -> str:
    value = unicodedata.normalize("NFKC", value.strip()).lower()
    value = re.sub(r"[^\w\-\s\u0080-\uffff]", "", value, flags=re.UNICODE)
    value = re.sub(r"[\s_]+", "-", value).strip("-")
    return value[:100] or "place"


def detect_language(path_lang: str | None = None) -> str:
    explicit = (path_lang or request.args.get("lang") or "").lower().split("-")[0]
    if explicit in LANGUAGES:
        return explicit
    for accepted, _quality in request.accept_languages:
        code = accepted.lower().split("-")[0]
        if code in LANGUAGES:
            return code
    return "en"


def resolve_context(
    path_lang: str | None = None,
    place_slug: str | None = None,
    date_str: str | None = None,
    *,
    allow_snapshot_time: bool = False,
) -> dict[str, Any]:
    """Resolve a live or user-selected Panchang instant.

    Live mode is the default. When ``live=0`` is supplied, the requested date
    and ``time=HH:MM`` are honoured so the edit form can freeze a calculation.
    The Open Graph renderer may always use its explicit snapshot minute.
    """
    lang = detect_language(path_lang)
    known = POPULAR_PLACES.get(place_slug or "", DEFAULT_PLACE)
    place_name = (request.args.get("place") or known["name"]).strip()[:120]
    latitude = clamp_float(request.args.get("lat"), float(known["latitude"]), -89.8, 89.8)
    longitude = clamp_float(request.args.get("lon"), float(known["longitude"]), -180.0, 180.0)
    tz_name, tz = safe_timezone(request.args.get("tz"), str(known["timezone"]))
    now = datetime.now(tz).replace(second=0, microsecond=0)
    selected_date = safe_date(date_str or request.args.get("date"), now.date())
    raw_live = (request.args.get("live") or "1").strip().lower()
    live = raw_live not in {"0", "false", "off", "no"}
    raw_time = request.args.get("time") if (allow_snapshot_time or not live) else None
    selected_time = safe_time(raw_time, now.timetz().replace(tzinfo=None)) if raw_time else now.timetz().replace(tzinfo=None)
    selected_at = datetime.combine(selected_date, selected_time, tzinfo=tz)
    # ZoneInfo accepts nonexistent wall times during a DST jump. Round-tripping
    # through UTC moves such a selection to the first real local instant.
    normalized_at = selected_at.astimezone(UTC).astimezone(tz)
    if (normalized_at.date(), normalized_at.hour, normalized_at.minute) != (selected_date, selected_time.hour, selected_time.minute):
        selected_at = normalized_at.replace(second=0, microsecond=0)
        selected_date = selected_at.date()
        selected_time = selected_at.timetz().replace(tzinfo=None)
    country = (request.args.get("country") or known.get("country") or "").strip()[:80]
    return {
        "lang": lang,
        "place": place_name or known["name"],
        "latitude": latitude,
        "longitude": longitude,
        "timezone": tz_name,
        "tz": tz,
        "date": selected_date,
        "time": selected_time,
        "at": selected_at,
        "live": live,
        "country": country,
        "slug": slugify_place(place_name or known["name"]),
    }


# ---------------------------------------------------------------------------
# Time formatting
# ---------------------------------------------------------------------------

EN_MONTHS = ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sept", "Oct", "Nov", "Dec"]
MONTH_NAMES_SHORT: dict[str, list[str]] = {
    "en": EN_MONTHS,
    "hi": ["जन", "फ़र", "मार्च", "अप्रैल", "मई", "जून", "जुलाई", "अग", "सित", "अक्त", "नव", "दिस"],
    "mr": ["जाने", "फेब्रु", "मार्च", "एप्रिल", "मे", "जून", "जुलै", "ऑग", "सप्टें", "ऑक्टो", "नोव्हें", "डिसें"],
    "gu": ["જાન", "ફેબ્રુ", "માર્ચ", "એપ્રિલ", "મે", "જૂન", "જુલાઈ", "ઑગ", "સપ્ટે", "ઑક્ટો", "નવે", "ડિસે"],
    "bn": ["জানু", "ফেব্রু", "মার্চ", "এপ্রিল", "মে", "জুন", "জুলাই", "আগ", "সেপ্টে", "অক্টো", "নভে", "ডিসে"],
    "ta": ["ஜன", "பிப்", "மார்ச்", "ஏப்", "மே", "ஜூன்", "ஜூலை", "ஆக", "செப்", "அக்", "நவ", "டிச"],
    "te": ["జన", "ఫిబ్ర", "మార్చి", "ఏప్రి", "మే", "జూన్", "జులై", "ఆగ", "సెప్టెం", "అక్టో", "నవం", "డిసెం"],
    "kn": ["ಜನ", "ಫೆಬ್ರ", "ಮಾರ್ಚ್", "ಏಪ್ರಿಲ್", "ಮೇ", "ಜೂನ್", "ಜುಲೈ", "ಆಗ", "ಸೆಪ್ಟೆಂ", "ಅಕ್ಟೋ", "ನವೆಂ", "ಡಿಸೆಂ"],
    "ml": ["ജനു", "ഫെബ്രു", "മാർച്ച്", "ഏപ്രിൽ", "മേയ്", "ജൂൺ", "ജൂലൈ", "ഓഗ", "സെപ്റ്റം", "ഒക്ടോ", "നവം", "ഡിസം"],
    "pa": ["ਜਨ", "ਫ਼ਰ", "ਮਾਰਚ", "ਅਪ੍ਰੈਲ", "ਮਈ", "ਜੂਨ", "ਜੁਲਾਈ", "ਅਗ", "ਸਤੰ", "ਅਕਤੂ", "ਨਵੰ", "ਦਸੰ"],
    "or": ["ଜାନୁ", "ଫେବ୍ରୁ", "ମାର୍ଚ୍ଚ", "ଏପ୍ରିଲ", "ମେ", "ଜୁନ", "ଜୁଲାଇ", "ଅଗ", "ସେପ୍ଟେ", "ଅକ୍ଟୋ", "ନଭେ", "ଡିସେ"],
    "ne": ["जन", "फेब्रु", "मार्च", "अप्रिल", "मे", "जुन", "जुलाई", "अग", "सेप्टे", "अक्टो", "नोभे", "डिसे"],
    "sa": ["जन", "फेब्रु", "मार्च", "अप्रैल", "मे", "जून", "जुलाई", "अग", "सित", "अक्त", "नव", "दिस"],
}
EN_WEEKDAYS = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday", "Sunday"]
WEEKDAY_NAMES: dict[str, list[str]] = {
    "en": EN_WEEKDAYS,
    "hi": ["सोमवार", "मंगलवार", "बुधवार", "गुरुवार", "शुक्रवार", "शनिवार", "रविवार"],
    "mr": ["सोमवार", "मंगळवार", "बुधवार", "गुरुवार", "शुक्रवार", "शनिवार", "रविवार"],
    "gu": ["સોમવાર", "મંગળવાર", "બુધવાર", "ગુરુવાર", "શુક્રવાર", "શનિવાર", "રવિવાર"],
    "bn": ["সোমবার", "মঙ্গলবার", "বুধবার", "বৃহস্পতিবার", "শুক্রবার", "শনিবার", "রবিবার"],
    "ta": ["திங்கள்", "செவ்வாய்", "புதன்", "வியாழன்", "வெள்ளி", "சனி", "ஞாயிறு"],
    "te": ["సోమవారం", "మంగళవారం", "బుధవారం", "గురువారం", "శుక్రవారం", "శనివారం", "ఆదివారం"],
    "kn": ["ಸೋಮವಾರ", "ಮಂಗಳವಾರ", "ಬುಧವಾರ", "ಗುರುವಾರ", "ಶುಕ್ರವಾರ", "ಶನಿವಾರ", "ಭಾನುವಾರ"],
    "ml": ["തിങ്കളാഴ്ച", "ചൊവ്വാഴ്ച", "ബുധനാഴ്ച", "വ്യാഴാഴ്ച", "വെള്ളിയാഴ്ച", "ശനിയാഴ്ച", "ഞായറാഴ്ച"],
    "pa": ["ਸੋਮਵਾਰ", "ਮੰਗਲਵਾਰ", "ਬੁੱਧਵਾਰ", "ਵੀਰਵਾਰ", "ਸ਼ੁੱਕਰਵਾਰ", "ਸ਼ਨੀਵਾਰ", "ਐਤਵਾਰ"],
    "or": ["ସୋମବାର", "ମଙ୍ଗଳବାର", "ବୁଧବାର", "ଗୁରୁବାର", "ଶୁକ୍ରବାର", "ଶନିବାର", "ରବିବାର"],
    "ne": ["सोमबार", "मंगलबार", "बुधबार", "बिहीबार", "शुक्रबार", "शनिबार", "आइतबार"],
    "sa": ["सोमवासरः", "मङ्गलवासरः", "बुधवासरः", "गुरुवासरः", "शुक्रवासरः", "शनिवासरः", "रविवासरः"],
}


def localized_weekday(value: date, lang: str) -> str:
    return WEEKDAY_NAMES.get(lang, EN_WEEKDAYS)[value.weekday()]


def ordinal(day: int) -> str:
    if 10 <= day % 100 <= 20:
        suffix = "th"
    else:
        suffix = {1: "st", 2: "nd", 3: "rd"}.get(day % 10, "th")
    return f"{day}{suffix}"


def format_clock(value: datetime) -> str:
    hour = value.hour % 12 or 12
    return f"{hour}:{value.minute:02d} {'AM' if value.hour < 12 else 'PM'}"


def localized_month(value: date | datetime, lang: str = "en") -> str:
    months = MONTH_NAMES_SHORT.get(lang, EN_MONTHS)
    return months[value.month - 1]


def format_date_label(value: date, lang: str = "en", include_year: bool = True) -> str:
    # Use one unambiguous Gregorian pattern in every language: 12 Sept 2026.
    core = f"{value.day} {localized_month(value, lang)}"
    return f"{core} {value.year}" if include_year else core


def format_header(value: datetime, place: str, lang: str) -> str:
    return f"{tr(lang, 'panchang')} ({place} - {format_date_label(value.date(), lang)} - {format_clock(value)})"


def format_compact_header(value: datetime, place: str, lang: str) -> str:
    # On narrow screens the page context is already obvious. Omitting the repeated
    # Panchang label preserves the complete place, date and time in every script.
    date_text = format_date_label(value.date(), lang)
    compact_hour = value.hour % 12 or 12
    compact_clock = f"{compact_hour}:{value.minute:02d} {'AM' if value.hour < 12 else 'PM'}"
    return f"{place} · {date_text} · {compact_clock}"


def format_card_date(value: date, lang: str = "en") -> str:
    """Compact, unambiguous date shown on every timeline card."""
    return f"{value.day} {localized_month(value, lang)} {value.year}"


def format_card_date_range(start: date, end: date, lang: str = "en") -> str:
    if start == end:
        return format_card_date(start, lang)
    if start.year == end.year and start.month == end.month:
        return f"{start.day}–{end.day} {localized_month(end, lang)} {end.year}"
    if start.year == end.year:
        return f"{start.day} {localized_month(start, lang)} – {end.day} {localized_month(end, lang)} {end.year}"
    return f"{format_card_date(start, lang)} – {format_card_date(end, lang)}"


def format_endpoint_display(value: datetime, lang: str = "en", include_year: bool = False) -> str:
    """Date-and-time endpoint for a cross-day card."""
    date_text = f"{value.day} {localized_month(value, lang)}"
    if include_year:
        date_text += f" {value.year}"
    return f"{date_text} · {format_clock(value)}"


def format_clock_range(start: datetime, end: datetime) -> str:
    """Format a readable range without repeating the same AM/PM marker."""
    offset_changes = start.utcoffset() != end.utcoffset()
    if offset_changes:
        start_clock = f"{format_clock(start)} {start.tzname() or ''}".strip()
        end_clock = f"{format_clock(end)} {end.tzname() or ''}".strip()
        return f"{start_clock} – {end_clock}"

    start_clock = format_clock(start)
    end_clock = format_clock(end)
    start_meridiem = start_clock.rsplit(" ", 1)[-1]
    end_meridiem = end_clock.rsplit(" ", 1)[-1]
    if start_meridiem == end_meridiem:
        start_clock = start_clock.rsplit(" ", 1)[0]
    return f"{start_clock} – {end_clock}"


def format_point(value: datetime, reference: date, lang: str = "en") -> str:
    del reference  # retained for backward-compatible internal calls
    return f"{format_card_date(value.date(), lang)} · {format_clock(value)}"


def format_range(start: datetime, end: datetime, reference: date, lang: str = "en") -> str:
    del reference  # retained for backward-compatible internal calls
    return f"{format_card_date_range(start.date(), end.date(), lang)} · {format_clock_range(start, end)}"


def iso_minute(value: datetime) -> str:
    return value.replace(microsecond=0).isoformat()


def shift_instant(value: datetime, delta: timedelta) -> datetime:
    """Move along absolute time while preserving the destination timezone."""
    return datetime.fromtimestamp(value.timestamp() + delta.total_seconds(), tz=value.tzinfo)


def instant_seconds(start: datetime, end: datetime) -> float:
    return end.timestamp() - start.timestamp()


def interpolate_instant(start: datetime, end: datetime, fraction: float) -> datetime:
    return datetime.fromtimestamp(
        start.timestamp() + instant_seconds(start, end) * fraction,
        tz=start.tzinfo,
    )


def instant_contains(start: datetime, moment: datetime, end: datetime) -> bool:
    stamp = moment.timestamp()
    return start.timestamp() <= stamp < end.timestamp()


def instant_before(left: datetime, right: datetime) -> bool:
    return left.timestamp() < right.timestamp()


# ---------------------------------------------------------------------------
# Astronomical calculations
# ---------------------------------------------------------------------------


def datetime_to_jd(value: datetime) -> float:
    utc = value.astimezone(UTC)
    decimal_hour = utc.hour + utc.minute / 60.0 + utc.second / 3600.0 + utc.microsecond / 3_600_000_000.0
    return swe.julday(utc.year, utc.month, utc.day, decimal_hour, swe.GREG_CAL)


def jd_to_datetime(jd: float, tz: ZoneInfo) -> datetime:
    year, month, day, decimal_hour = swe.revjul(jd, swe.GREG_CAL)
    hour = int(decimal_hour)
    minute_float = (decimal_hour - hour) * 60.0
    minute = int(minute_float)
    second = int(round((minute_float - minute) * 60.0))
    if second >= 60:
        second -= 60
        minute += 1
    if minute >= 60:
        minute -= 60
        hour += 1
    base = datetime(year, month, day, tzinfo=UTC) + timedelta(hours=hour, minutes=minute, seconds=second)
    return base.astimezone(tz)


@lru_cache(maxsize=150_000)
def _sun_moon_for_epoch(epoch_second: int) -> tuple[float, float]:
    utc = datetime.fromtimestamp(epoch_second, tz=UTC)
    jd = datetime_to_jd(utc)
    sun = swe.calc_ut(jd, swe.SUN, ASTRO_FLAGS)[0][0] % 360.0
    moon = swe.calc_ut(jd, swe.MOON, ASTRO_FLAGS)[0][0] % 360.0
    return sun, moon


@lru_cache(maxsize=80_000)
def _ascendant_for_epoch(epoch_second: int, lat_key: float, lon_key: float) -> float:
    utc = datetime.fromtimestamp(epoch_second, tz=UTC)
    jd = datetime_to_jd(utc)
    try:
        _cusps, ascmc = swe.houses_ex(jd, lat_key, lon_key, b"W", swe.FLG_SIDEREAL)
        return ascmc[0] % 360.0
    except swe.Error:
        _cusps, ascmc = swe.houses_ex(jd, max(-65.0, min(65.0, lat_key)), lon_key, b"E", swe.FLG_SIDEREAL)
        return ascmc[0] % 360.0


def sun_moon(value: datetime) -> tuple[float, float]:
    return _sun_moon_for_epoch(int(round(value.timestamp())))


def ascendant(value: datetime, latitude: float, longitude: float) -> float:
    return _ascendant_for_epoch(int(round(value.timestamp())), round(latitude, 5), round(longitude, 5))


def category_index(kind: str, value: datetime, latitude: float, longitude: float) -> int:
    if kind == "lagna":
        return int(ascendant(value, latitude, longitude) // 30.0) % 12
    sun, moon = sun_moon(value)
    phase = (moon - sun) % 360.0
    if kind == "tithi":
        return int(phase // 12.0) % 30
    if kind == "nakshatra":
        return int(moon // (360.0 / 27.0)) % 27
    if kind == "yoga":
        return int(((sun + moon) % 360.0) // (360.0 / 27.0)) % 27
    if kind == "karana":
        return int(phase // 6.0) % 60
    raise ValueError(f"Unknown category: {kind}")


def find_category_boundary(
    kind: str,
    value: datetime,
    direction: int,
    latitude: float,
    longitude: float,
) -> datetime:
    """Find the previous/next category boundary to roughly 20-second precision."""
    if direction not in {-1, 1}:
        raise ValueError("direction must be -1 or 1")
    current = category_index(kind, value, latitude, longitude)
    step_seconds = 300.0 if kind == "lagna" else 1800.0
    max_hours = 10 if kind == "lagna" else (40 if kind == "karana" else 72)
    cursor_stamp = value.timestamp()
    iterations = int(max_hours * 3600 / step_seconds) + 2
    tz = value.tzinfo
    for _ in range(iterations):
        probe_stamp = cursor_stamp + direction * step_seconds
        probe = datetime.fromtimestamp(probe_stamp, tz=tz)
        if category_index(kind, probe, latitude, longitude) != current:
            if direction > 0:
                left_stamp, right_stamp = cursor_stamp, probe_stamp  # current, other
                while right_stamp - left_stamp > 20:
                    mid_stamp = (left_stamp + right_stamp) / 2
                    mid = datetime.fromtimestamp(mid_stamp, tz=tz)
                    if category_index(kind, mid, latitude, longitude) == current:
                        left_stamp = mid_stamp
                    else:
                        right_stamp = mid_stamp
                return datetime.fromtimestamp(right_stamp, tz=tz).replace(microsecond=0)
            left_stamp, right_stamp = probe_stamp, cursor_stamp  # other, current
            while right_stamp - left_stamp > 20:
                mid_stamp = (left_stamp + right_stamp) / 2
                mid = datetime.fromtimestamp(mid_stamp, tz=tz)
                if category_index(kind, mid, latitude, longitude) == current:
                    right_stamp = mid_stamp
                else:
                    left_stamp = mid_stamp
            return datetime.fromtimestamp(right_stamp, tz=tz).replace(microsecond=0)
        cursor_stamp = probe_stamp
    fallback = timedelta(hours=max_hours)
    return shift_instant(value, fallback if direction > 0 else -fallback)


def karana_key(index: int) -> str:
    if index == 0:
        return "kimstughna"
    if 1 <= index <= 56:
        movable = ["bava", "balava", "kaulava", "taitila", "garaja", "vanija", "vishti"]
        return movable[(index - 1) % 7]
    return {57: "shakuni", 58: "chatushpada", 59: "nagava"}[index]


def category_title(kind: str, index: int, lang: str) -> str:
    if kind == "tithi":
        paksha = "shukla" if index < 15 else "krishna"
        within = index if index < 15 else index - 15
        if index == 29:
            tithi_pair = ("Amāvāsyā", "Amavasya")
        else:
            tithi_pair = TITHI_NAMES[within]
        return join_localized([PAKSHA_NAMES[paksha], tithi_pair], lang)
    if kind == "nakshatra":
        return localize_sanskrit(NAKSHATRA_NAMES[index], lang)
    if kind == "yoga":
        return localize_sanskrit(YOGA_NAMES[index], lang)
    if kind == "karana":
        return localize_sanskrit(KARANA_NAMES[karana_key(index)], lang)
    if kind == "lagna":
        lagna_word = ("Lagna", "Lagna")
        return join_localized([RASHI_NAMES[index], lagna_word], lang)
    return str(index)


def category_quality(kind: str, index: int) -> str:
    if kind == "yoga":
        bad = {0, 5, 8, 9, 12, 14, 16, 18, 26}
        good = {1, 2, 3, 4, 6, 7, 10, 11, 13, 15, 17, 19, 20, 21, 22, 23, 24, 25}
        if index in bad:
            return "inauspicious"
        if index in good:
            return "auspicious"
    if kind == "karana":
        key = karana_key(index)
        if key in {"vishti", "shakuni", "chatushpada", "nagava", "kimstughna"}:
            return "inauspicious"
        return "auspicious"
    return "neutral"


def interval_item(
    title: str,
    start: datetime,
    end: datetime,
    at: datetime,
    lang: str,
    quality: str = "neutral",
    focus: bool | None = None,
    detail: str = "",
) -> dict[str, Any]:
    current = instant_contains(start, at, end) if focus is None else focus
    date_text = format_card_date_range(start.date(), end.date(), lang)
    clock_text = format_clock_range(start, end)
    endpoint_year = True
    start_display = format_endpoint_display(start, lang, endpoint_year)
    end_display = format_endpoint_display(end, lang, endpoint_year)
    return {
        "title": title,
        "date": date_text,
        "clock": clock_text,
        # A machine-readable and screen-reader-friendly representation that
        # always binds each clock time to its own date.
        "time": f"{start_display} → {end_display}",
        "start_display": start_display,
        "end_display": end_display,
        "crosses_day": start.date() != end.date(),
        "start": iso_minute(start),
        "end": iso_minute(end),
        "current": bool(current),
        "quality": quality,
        "detail": detail,
        "badge": tr(lang, "now") if current else "",
    }


def _timeline_widths(duration_minutes: int) -> tuple[int, int, int]:
    """Map elapsed minutes to a readable visual timeline.

    A complete civil day occupies one consistent visual span per viewport.
    Short periods retain a minimum width so their date and time remain
    readable, while all longer periods grow directly with their duration.
    Cross-midnight intervals remain intact and use their full real duration.
    """
    minutes = max(1, int(duration_minutes))
    desktop = max(176, min(1080, round(minutes * (1080 / 1440))))
    mobile = max(182, min(760, round(minutes * (760 / 1440))))
    landscape = max(160, min(900, round(minutes * (900 / 1440))))
    return desktop, mobile, landscape


def _decorate_timeline_item(item: dict[str, Any], duration_minutes: int, day_key: str, starts_day: bool) -> dict[str, Any]:
    decorated = dict(item)
    desktop, mobile, landscape = _timeline_widths(duration_minutes)
    decorated.update({
        "duration_minutes": duration_minutes,
        "width_px": desktop,
        "mobile_width_px": mobile,
        "landscape_width_px": landscape,
        "day_key": day_key,
        "starts_day": bool(starts_day),
    })
    return decorated


def decorate_timeline_items(items: list[dict[str, Any]], at: datetime, lang: str) -> list[dict[str, Any]]:
    """Decorate real Panchang intervals without inventing midnight boundaries.

    Midnight is a civil-clock boundary, not a Tithi, Nakshatra, Yoga, Karana,
    Choghadiya, Hora, Muhurta or Lagna transition.  Each calculated interval
    therefore remains one card from its true start instant to its true end
    instant.  Cross-day cards carry an explicit start date/time and end
    date/time so users never have to guess which day a clock value belongs to.
    """
    result: list[dict[str, Any]] = []
    local_tz = at.tzinfo

    for item in items:
        # Daily sunrise/sunset and unavailable cards intentionally represent a
        # complete civil date rather than an interval transition.
        if item.get("fixed_day_card") or not item.get("start") or not item.get("end"):
            day_key = str(item.get("day_key") or at.date().isoformat())
            duration = int(item.get("duration_minutes") or 1440)
            fixed = dict(item)
            fixed.setdefault("crosses_day", False)
            fixed.setdefault("start_display", "")
            fixed.setdefault("end_display", "")
            result.append(_decorate_timeline_item(
                fixed,
                duration,
                day_key,
                bool(item.get("starts_day", True)),
            ))
            continue

        try:
            start = datetime.fromisoformat(str(item["start"])).astimezone(local_tz)
            end = datetime.fromisoformat(str(item["end"])).astimezone(local_tz)
        except (TypeError, ValueError):
            fallback = dict(item)
            fallback.setdefault("crosses_day", False)
            fallback.setdefault("start_display", "")
            fallback.setdefault("end_display", "")
            result.append(_decorate_timeline_item(fallback, 240, at.date().isoformat(), False))
            continue

        duration = max(1, int(round((end.timestamp() - start.timestamp()) / 60.0)))
        if end.timestamp() <= start.timestamp():
            duration = 1

        decorated = dict(item)
        endpoint_year = start.year != end.year
        start_display = format_endpoint_display(start, lang, endpoint_year)
        end_display = format_endpoint_display(end, lang, endpoint_year)
        decorated.update({
            "date": format_card_date_range(start.date(), end.date(), lang),
            "clock": format_clock_range(start, end),
            "time": f"{start_display} → {end_display}",
            "start_display": start_display,
            "end_display": end_display,
            "crosses_day": start.date() != end.date(),
            "start": iso_minute(start),
            "end": iso_minute(end),
            "current": instant_contains(start, at, end),
            "continues_previous": False,
            "continues_next": False,
        })
        result.append(_decorate_timeline_item(
            decorated,
            duration,
            start.date().isoformat(),
            False,
        ))

    return result

def make_category_timeline(kind: str, at: datetime, latitude: float, longitude: float, lang: str, before: int = TIMELINE_PAST_ITEMS, after: int = TIMELINE_FUTURE_ITEMS) -> list[dict[str, Any]]:
    current_index = category_index(kind, at, latitude, longitude)
    current_start = find_category_boundary(kind, at, -1, latitude, longitude)
    current_end = find_category_boundary(kind, at, 1, latitude, longitude)
    raw: list[tuple[int, datetime, datetime, bool]] = [(current_index, current_start, current_end, True)]

    cursor_start = current_start
    for _ in range(before):
        probe = shift_instant(cursor_start, -timedelta(minutes=2))
        idx = category_index(kind, probe, latitude, longitude)
        start = find_category_boundary(kind, probe, -1, latitude, longitude)
        raw.insert(0, (idx, start, cursor_start, False))
        cursor_start = start

    cursor_end = current_end
    for _ in range(after):
        probe = shift_instant(cursor_end, timedelta(minutes=2))
        idx = category_index(kind, probe, latitude, longitude)
        end = find_category_boundary(kind, probe, 1, latitude, longitude)
        raw.append((idx, cursor_end, end, False))
        cursor_end = end

    items = []
    for idx, start, end, is_current in raw:
        item = interval_item(
            category_title(kind, idx, lang), start, end, at, lang,
            quality=category_quality(kind, idx), focus=is_current,
        )
        item["index"] = idx
        items.append(item)
    return items


@lru_cache(maxsize=20_000)
def _sun_event_cached(date_iso: str, lat_key: float, lon_key: float, tz_name: str, event: str) -> str | None:
    local_date = date.fromisoformat(date_iso)
    tz = ZoneInfo(tz_name)
    midnight = datetime.combine(local_date, dt_time.min, tzinfo=tz)
    search_jd = datetime_to_jd(midnight - timedelta(hours=2))
    rsmi = swe.CALC_RISE if event == "rise" else swe.CALC_SET
    try:
        result, times = swe.rise_trans(
            search_jd,
            swe.SUN,
            rsmi,
            (lon_key, lat_key, 0.0),
            0.0,
            15.0,
            RISE_SET_FLAGS,
        )
        if result != 0:
            return None
        local = jd_to_datetime(times[0], tz)
        # A two-hour early search can return the same civil date reliably. If it
        # returns outside the date (polar regions), consider the event absent.
        if local.date() != local_date:
            return None
        return local.isoformat()
    except (swe.Error, ValueError, OverflowError):
        return None


def sun_event(local_date: date, latitude: float, longitude: float, tz_name: str, event: str) -> datetime | None:
    result = _sun_event_cached(local_date.isoformat(), round(latitude, 5), round(longitude, 5), tz_name, event)
    if not result:
        return None
    # fromisoformat preserves only the numeric offset. Reattach the IANA zone so
    # interpolation across DST transitions produces real local wall times.
    return datetime.fromisoformat(result).astimezone(ZoneInfo(tz_name))


def sun_pair(local_date: date, latitude: float, longitude: float, tz_name: str) -> tuple[datetime | None, datetime | None]:
    return (
        sun_event(local_date, latitude, longitude, tz_name, "rise"),
        sun_event(local_date, latitude, longitude, tz_name, "set"),
    )


def point_item(title: str, value: datetime | None, at: datetime, lang: str, focus: bool) -> dict[str, Any]:
    if value is None:
        date_text = format_card_date(at.date(), lang)
        clock_text = tr(lang, "solar_unavailable")
        return {
            "title": title, "date": date_text, "clock": clock_text, "time": f"{date_text} · {clock_text}",
            "start": "", "end": "", "current": focus, "quality": "neutral", "detail": "",
            "badge": tr(lang, "selected") if focus else "",
        }
    date_text = format_card_date(value.date(), lang)
    clock_text = format_clock(value)
    return {
        "title": title,
        "date": date_text,
        "clock": clock_text,
        "time": f"{date_text} · {clock_text}",
        "start": iso_minute(value),
        "end": "",
        "current": focus,
        "quality": "neutral",
        "detail": "",
        "badge": (tr(lang, "today") if value.date() == datetime.now(value.tzinfo).date() else tr(lang, "selected")) if focus else "",
    }


def make_sun_timeline(event: str, at: datetime, latitude: float, longitude: float, tz_name: str, lang: str) -> list[dict[str, Any]]:
    items = []
    for offset in range(-TIMELINE_PAST_ITEMS, TIMELINE_FUTURE_ITEMS + 1):
        day = at.date() + timedelta(days=offset)
        value = sun_event(day, latitude, longitude, tz_name, event)
        weekday = localized_weekday(day, lang)
        title = weekday
        items.append(point_item(title, value, at, lang, offset == 0))
    return items


def make_sunrise_sunset_timeline(
    at: datetime,
    latitude: float,
    longitude: float,
    tz_name: str,
    lang: str,
) -> list[dict[str, Any]]:
    """Return one daily card containing both local sunrise and sunset."""
    items: list[dict[str, Any]] = []
    for offset in range(-TIMELINE_PAST_ITEMS, TIMELINE_FUTURE_ITEMS + 1):
        day = at.date() + timedelta(days=offset)
        sunrise, sunset = sun_pair(day, latitude, longitude, tz_name)
        title = localized_weekday(day, lang)
        date_text = format_card_date(day, lang)
        sunrise_text = format_clock(sunrise) if sunrise else "—"
        sunset_text = format_clock(sunset) if sunset else "—"
        clock_text = f"{sunrise_text} · {sunset_text}"
        items.append({
            "title": title,
            "date": date_text,
            "clock": clock_text,
            "time": f"{date_text} · {clock_text}",
            "start": iso_minute(sunrise) if sunrise else "",
            "end": iso_minute(sunset) if sunset else "",
            "current": offset == 0,
            "quality": "neutral",
            "detail": "",
            "badge": "",
            "sunrise_time": sunrise_text,
            "sunset_time": sunset_text,
            "duration_minutes": 1440,
            "day_key": day.isoformat(),
            "starts_day": True,
            "fixed_day_card": True,
        })
    return items


# ---------------------------------------------------------------------------
# Choghadiya, Hora and special periods
# ---------------------------------------------------------------------------

DAY_CHOGHADIYA_CYCLE = ["udveg", "chal", "labh", "amrit", "kaal", "shubh", "rog"]
NIGHT_CHOGHADIYA_CYCLE = ["shubh", "amrit", "chal", "rog", "kaal", "labh", "udveg"]
DAY_CHOGHADIYA_START = [3, 6, 2, 5, 1, 4, 0]  # Monday ... Sunday
NIGHT_CHOGHADIYA_START = [2, 4, 6, 1, 3, 5, 0]


def rotated_sequence(cycle: list[str], start: int, count: int) -> list[str]:
    return [cycle[(start + i) % len(cycle)] for i in range(count)]


def choghadiya_quality(key: str) -> str:
    if key in {"amrit", "shubh", "labh"}:
        return "auspicious"
    if key in {"rog", "kaal", "udveg"}:
        return "inauspicious"
    return "neutral"


def all_choghadiya_segments(at: datetime, latitude: float, longitude: float, tz_name: str, lang: str) -> list[dict[str, Any]]:
    segments: list[dict[str, Any]] = []
    for offset in range(-4, 6):
        day = at.date() + timedelta(days=offset)
        sunrise, sunset = sun_pair(day, latitude, longitude, tz_name)
        next_sunrise = sun_event(day + timedelta(days=1), latitude, longitude, tz_name, "rise")
        if not sunrise or not sunset or not next_sunrise:
            continue
        if not (instant_before(sunrise, sunset) and instant_before(sunset, next_sunrise)):
            continue
        day_names = rotated_sequence(DAY_CHOGHADIYA_CYCLE, DAY_CHOGHADIYA_START[day.weekday()], 8)
        night_names = rotated_sequence(NIGHT_CHOGHADIYA_CYCLE, NIGHT_CHOGHADIYA_START[day.weekday()], 8)
        for i, key in enumerate(day_names):
            start_time = interpolate_instant(sunrise, sunset, i / 8)
            end_time = interpolate_instant(sunrise, sunset, (i + 1) / 8)
            segments.append({"key": key, "start": start_time, "end": end_time, "phase": tr(lang, "daytime")})
        for i, key in enumerate(night_names):
            start_time = interpolate_instant(sunset, next_sunrise, i / 8)
            end_time = interpolate_instant(sunset, next_sunrise, (i + 1) / 8)
            segments.append({"key": key, "start": start_time, "end": end_time, "phase": tr(lang, "nighttime")})
    return sorted(segments, key=lambda x: x["start"].timestamp())


def select_timeline_window(segments: list[dict[str, Any]], at: datetime, before: int = TIMELINE_PAST_ITEMS, after: int = TIMELINE_FUTURE_ITEMS) -> list[dict[str, Any]]:
    if not segments:
        return []
    index = next((i for i, item in enumerate(segments) if instant_contains(item["start"], at, item["end"])), None)
    if index is None:
        index = min(range(len(segments)), key=lambda i: abs(segments[i]["start"].timestamp() - at.timestamp()))
    start = max(0, index - before)
    end = min(len(segments), index + after + 1)
    return segments[start:end]


def unavailable_timeline(at: datetime, lang: str) -> list[dict[str, Any]]:
    # Polar regions can have no sunrise or sunset for several days. Keep the
    # interaction contract intact with four past, one selected and twelve
    # future date cards while clearly stating that solar divisions are absent.
    items: list[dict[str, Any]] = []
    for offset in range(-TIMELINE_PAST_ITEMS, TIMELINE_FUTURE_ITEMS + 1):
        day = at.date() + timedelta(days=offset)
        date_text = format_card_date(day, lang)
        clock_text = tr(lang, "solar_unavailable")
        items.append({
            "title": f"{localized_weekday(day, lang)} · {tr(lang, 'not_available')}",
            "date": date_text,
            "clock": clock_text,
            "time": f"{date_text} · {clock_text}",
            "start": "",
            "end": "",
            "current": offset == 0,
            "quality": "neutral",
            "detail": "",
            "badge": tr(lang, "selected") if offset == 0 else "",
            "duration_minutes": 1440,
            "day_key": day.isoformat(),
            "starts_day": True,
            "fixed_day_card": True,
        })
    return items


def make_choghadiya_timeline(at: datetime, latitude: float, longitude: float, tz_name: str, lang: str) -> list[dict[str, Any]]:
    segments = select_timeline_window(all_choghadiya_segments(at, latitude, longitude, tz_name, lang), at)
    if not segments:
        return unavailable_timeline(at, lang)
    items = []
    for seg in segments:
        title = localize_sanskrit(CHOGHADIYA_NAMES[seg["key"]], lang)
        current = instant_contains(seg["start"], at, seg["end"])
        item = interval_item(title, seg["start"], seg["end"], at, lang, choghadiya_quality(seg["key"]), focus=current, detail=seg["phase"])
        items.append(item)
    return items


PLANETARY_ORDER = ["saturn", "jupiter", "mars", "sun", "venus", "mercury", "moon"]
WEEKDAY_LORD_START = [6, 2, 5, 1, 4, 0, 3]  # Monday ... Sunday


def hora_quality(planet: str) -> str:
    if planet in {"jupiter", "venus", "mercury", "moon"}:
        return "auspicious"
    if planet in {"mars", "saturn"}:
        return "inauspicious"
    return "neutral"


def all_hora_segments(at: datetime, latitude: float, longitude: float, tz_name: str, lang: str) -> list[dict[str, Any]]:
    segments: list[dict[str, Any]] = []
    for offset in range(-4, 6):
        day = at.date() + timedelta(days=offset)
        sunrise, sunset = sun_pair(day, latitude, longitude, tz_name)
        next_sunrise = sun_event(day + timedelta(days=1), latitude, longitude, tz_name, "rise")
        if not sunrise or not sunset or not next_sunrise:
            continue
        if not (instant_before(sunrise, sunset) and instant_before(sunset, next_sunrise)):
            continue
        start_index = WEEKDAY_LORD_START[day.weekday()]
        for i in range(12):
            planet = PLANETARY_ORDER[(start_index + i) % 7]
            segments.append({
                "planet": planet,
                "start": interpolate_instant(sunrise, sunset, i / 12),
                "end": interpolate_instant(sunrise, sunset, (i + 1) / 12),
                "phase": tr(lang, "daytime"),
            })
        for i in range(12):
            planet = PLANETARY_ORDER[(start_index + 12 + i) % 7]
            segments.append({
                "planet": planet,
                "start": interpolate_instant(sunset, next_sunrise, i / 12),
                "end": interpolate_instant(sunset, next_sunrise, (i + 1) / 12),
                "phase": tr(lang, "nighttime"),
            })
    return sorted(segments, key=lambda x: x["start"].timestamp())


def make_hora_timeline(at: datetime, latitude: float, longitude: float, tz_name: str, lang: str) -> list[dict[str, Any]]:
    segments = select_timeline_window(all_hora_segments(at, latitude, longitude, tz_name, lang), at)
    if not segments:
        return unavailable_timeline(at, lang)
    items = []
    hora_pair = ("Horā", "Hora")
    for seg in segments:
        title = join_localized([PLANET_NAMES[seg["planet"]], hora_pair], lang)
        current = instant_contains(seg["start"], at, seg["end"])
        items.append(interval_item(title, seg["start"], seg["end"], at, lang, hora_quality(seg["planet"]), focus=current, detail=seg["phase"]))
    return items


RAHU_SEGMENT = [1, 6, 4, 5, 3, 2, 7]       # zero-based day eighth, Monday ... Sunday
YAMAGANDA_SEGMENT = [3, 2, 1, 0, 6, 5, 4]
GULIKA_SEGMENT = [5, 4, 3, 2, 1, 0, 6]
PERIOD_PRIORITY = {
    "rahu": 1, "yamaganda": 2, "gulika": 3, "abhijit": 4, "vijaya": 5,
    "brahma": 6, "nishita": 7, "godhuli": 8, "pratah": 9, "sayahna": 10,
}


def add_period(target: list[dict[str, Any]], key: str, start: datetime, end: datetime, quality: str) -> None:
    if instant_before(start, end):
        target.append({"key": key, "start": start, "end": end, "quality": quality})


def special_periods_for_day(day: date, latitude: float, longitude: float, tz_name: str) -> list[dict[str, Any]]:
    sunrise, sunset = sun_pair(day, latitude, longitude, tz_name)
    previous_sunset = sun_event(day - timedelta(days=1), latitude, longitude, tz_name, "set")
    next_sunrise = sun_event(day + timedelta(days=1), latitude, longitude, tz_name, "rise")
    if not sunrise or not sunset or not previous_sunset or not next_sunrise:
        return []
    if not (
        instant_before(previous_sunset, sunrise)
        and instant_before(sunrise, sunset)
        and instant_before(sunset, next_sunrise)
    ):
        return []
    periods: list[dict[str, Any]] = []
    daylight_seconds = instant_seconds(sunrise, sunset)
    night_before_seconds = instant_seconds(previous_sunset, sunrise)
    night_after_seconds = instant_seconds(sunset, next_sunrise)

    add_period(
        periods, "brahma",
        shift_instant(sunrise, -timedelta(seconds=2 * night_before_seconds / 15)),
        shift_instant(sunrise, -timedelta(seconds=night_before_seconds / 15)),
        "auspicious",
    )
    add_period(
        periods, "pratah",
        shift_instant(sunrise, -timedelta(seconds=night_before_seconds / 15)),
        sunrise,
        "auspicious",
    )
    add_period(periods, "abhijit", interpolate_instant(sunrise, sunset, 7 / 15), interpolate_instant(sunrise, sunset, 8 / 15), "auspicious")
    add_period(periods, "vijaya", interpolate_instant(sunrise, sunset, 10 / 15), interpolate_instant(sunrise, sunset, 11 / 15), "auspicious")

    for key, table in (("rahu", RAHU_SEGMENT), ("yamaganda", YAMAGANDA_SEGMENT), ("gulika", GULIKA_SEGMENT)):
        idx = table[day.weekday()]
        add_period(periods, key, interpolate_instant(sunrise, sunset, idx / 8), interpolate_instant(sunrise, sunset, (idx + 1) / 8), "inauspicious")

    add_period(
        periods, "godhuli",
        shift_instant(sunset, -timedelta(seconds=daylight_seconds / 30)),
        shift_instant(sunset, timedelta(seconds=night_after_seconds / 30)),
        "auspicious",
    )
    add_period(periods, "sayahna", sunset, shift_instant(sunset, timedelta(seconds=night_after_seconds / 15)), "auspicious")
    night_midpoint = interpolate_instant(sunset, next_sunrise, 1 / 2)
    add_period(
        periods, "nishita",
        shift_instant(night_midpoint, -timedelta(seconds=night_after_seconds / 30)),
        shift_instant(night_midpoint, timedelta(seconds=night_after_seconds / 30)),
        "auspicious",
    )
    return periods


def is_daylight(moment: datetime, latitude: float, longitude: float, tz_name: str) -> bool:
    sunrise, sunset = sun_pair(moment.date(), latitude, longitude, tz_name)
    return bool(sunrise and sunset and instant_contains(sunrise, moment, sunset))


def all_period_segments(at: datetime, latitude: float, longitude: float, tz_name: str, lang: str) -> list[dict[str, Any]]:
    specials: list[dict[str, Any]] = []
    for offset in range(-4, 7):
        specials.extend(special_periods_for_day(at.date() + timedelta(days=offset), latitude, longitude, tz_name))

    range_start = datetime.combine(at.date() - timedelta(days=3), dt_time.min, tzinfo=at.tzinfo)
    range_end = datetime.combine(at.date() + timedelta(days=7), dt_time.min, tzinfo=at.tzinfo)
    boundary_by_stamp: dict[float, datetime] = {
        range_start.timestamp(): range_start,
        range_end.timestamp(): range_end,
    }
    for item in specials:
        if item["end"].timestamp() > range_start.timestamp() and item["start"].timestamp() < range_end.timestamp():
            clipped_start = item["start"] if item["start"].timestamp() >= range_start.timestamp() else range_start
            clipped_end = item["end"] if item["end"].timestamp() <= range_end.timestamp() else range_end
            boundary_by_stamp[clipped_start.timestamp()] = clipped_start
            boundary_by_stamp[clipped_end.timestamp()] = clipped_end
    ordered = [boundary_by_stamp[stamp] for stamp in sorted(boundary_by_stamp)]
    segments: list[dict[str, Any]] = []
    for left, right in zip(ordered, ordered[1:]):
        if not instant_before(left, right):
            continue
        midpoint = interpolate_instant(left, right, 1 / 2)
        active = [item for item in specials if instant_contains(item["start"], midpoint, item["end"])]
        active.sort(key=lambda item: PERIOD_PRIORITY.get(item["key"], 99))
        if active:
            keys = tuple(item["key"] for item in active)
            quality = "inauspicious" if any(item["quality"] == "inauspicious" for item in active) else "auspicious"
        else:
            keys = ("daytime" if is_daylight(midpoint, latitude, longitude, tz_name) else "nighttime",)
            quality = "neutral"
        if (
            segments
            and segments[-1]["keys"] == keys
            and segments[-1]["quality"] == quality
            and abs(segments[-1]["end"].timestamp() - left.timestamp()) < 0.5
        ):
            segments[-1]["end"] = right
        else:
            segments.append({"keys": keys, "start": left, "end": right, "quality": quality})
    return segments


def make_period_timeline(at: datetime, latitude: float, longitude: float, tz_name: str, lang: str) -> list[dict[str, Any]]:
    sunrise, sunset = sun_pair(at.date(), latitude, longitude, tz_name)
    if not sunrise or not sunset:
        return unavailable_timeline(at, lang)
    segments = select_timeline_window(all_period_segments(at, latitude, longitude, tz_name, lang), at)
    if not segments:
        return unavailable_timeline(at, lang)
    items: list[dict[str, Any]] = []
    for seg in segments:
        names = [localize_sanskrit(PERIOD_NAMES[key], lang) for key in seg["keys"]]
        title = " + ".join(names)
        current = instant_contains(seg["start"], at, seg["end"])
        quality = seg["quality"]
        if len(seg["keys"]) > 1 and quality == "inauspicious" and any(
            key in {"abhijit", "vijaya", "brahma", "godhuli", "nishita"} for key in seg["keys"]
        ):
            detail = tr(lang, "mixed")
        else:
            detail = ""
        items.append(interval_item(title, seg["start"], seg["end"], at, lang, quality, focus=current, detail=detail))
    return items

# ---------------------------------------------------------------------------
# Panchang response model and SEO
# ---------------------------------------------------------------------------

SECTION_ICONS = {
    "sunrise_sunset": "☀", "sunrise": "☀", "sunset": "◒", "tithi": "◐", "nakshatra": "✦", "yoga": "∞",
    "karana": "◇", "choghadiya": "◷", "hora": "☉", "period": "ॐ", "lagna": "↟",
}


def current_or_focused(items: list[dict[str, Any]]) -> dict[str, Any]:
    return next((item for item in items if item.get("current")), items[len(items) // 2] if items else {})


def section_model(key: str, label: str, items: list[dict[str, Any]]) -> dict[str, Any]:
    return {"key": key, "label": label, "icon": SECTION_ICONS[key], "items": items}


def build_panchang(context: dict[str, Any]) -> dict[str, Any]:
    at: datetime = context["at"]
    lat = context["latitude"]
    lon = context["longitude"]
    tz_name = context["timezone"]
    lang = context["lang"]

    sun_items = make_sunrise_sunset_timeline(at, lat, lon, tz_name, lang)
    sections = [
        section_model("sunrise_sunset", f"{tr(lang, 'sunrise')} / {tr(lang, 'sunset')}", sun_items),
        section_model("tithi", tr(lang, "tithi"), make_category_timeline("tithi", at, lat, lon, lang)),
        section_model("nakshatra", tr(lang, "nakshatra"), make_category_timeline("nakshatra", at, lat, lon, lang)),
        section_model("yoga", tr(lang, "yoga"), make_category_timeline("yoga", at, lat, lon, lang)),
        section_model("karana", tr(lang, "karana"), make_category_timeline("karana", at, lat, lon, lang)),
        section_model("choghadiya", tr(lang, "choghadiya"), make_choghadiya_timeline(at, lat, lon, tz_name, lang)),
        section_model("hora", tr(lang, "hora"), make_hora_timeline(at, lat, lon, tz_name, lang)),
        section_model("period", tr(lang, "period"), make_period_timeline(at, lat, lon, tz_name, lang)),
        section_model("lagna", tr(lang, "lagna"), make_category_timeline("lagna", at, lat, lon, lang)),
    ]
    for section in sections:
        section["items"] = decorate_timeline_items(section["items"], at, lang)

    summary = {section["key"]: current_or_focused(section["items"]) for section in sections}
    sun_focus = current_or_focused(sun_items)
    summary["sunrise"] = {"time": sun_focus.get("sunrise_time", "")}
    summary["sunset"] = {"time": sun_focus.get("sunset_time", "")}
    headers = {
        "previous": format_header(at - timedelta(days=1), context["place"], lang),
        "current": format_header(at, context["place"], lang),
        "next": format_header(at + timedelta(days=1), context["place"], lang),
    }
    headers_compact = {
        "previous": format_compact_header(at - timedelta(days=1), context["place"], lang),
        "current": format_compact_header(at, context["place"], lang),
        "next": format_compact_header(at + timedelta(days=1), context["place"], lang),
    }
    return {
        "app": {"name": APP_NAME, "version": APP_VERSION},
        "query": {
            "place": context["place"], "slug": context["slug"], "lat": round(lat, 6), "lon": round(lon, 6),
            "timezone": tz_name, "date": at.date().isoformat(), "date_display": format_card_date(at.date(), lang), "time": at.strftime("%H:%M"),
            "language": lang, "live": context["live"], "country": context["country"],
        },
        "headers": headers,
        "headers_compact": headers_compact,
        "default_location": {
            "name": DEFAULT_PLACE["name"], "lat": DEFAULT_PLACE["latitude"], "lon": DEFAULT_PLACE["longitude"],
            "timezone": DEFAULT_PLACE["timezone"], "country": DEFAULT_PLACE["country"], "slug": "ujjain",
        },
        "timeline_window": {"past": TIMELINE_PAST_ITEMS, "upcoming": TIMELINE_FUTURE_ITEMS},
        "sections": sections,
        "summary": summary,
        "ui": ui_text(lang),
        "months": MONTH_NAMES_SHORT.get(lang, EN_MONTHS),
        "month_names": MONTH_NAMES_SHORT,
        "languages": [
            {"code": code, "name": info["name"], "native": info["native"]}
            for code, info in LANGUAGES.items()
        ],
        "generated_at": datetime.now(UTC).replace(microsecond=0).isoformat(),
        "method": "Lahiri ayanamsa; Swiss Ephemeris Moshier; local sunrise/sunset; traditional Choghadiya, Hora and Muhurta divisions",
    }


def site_root() -> str:
    # Keep local development self-contained, but use the custom production
    # domain everywhere else.  This prevents Safari/WhatsApp shares from
    # exposing the Render service hostname.
    try:
        host = (request.host or "").split(":", 1)[0].lower()
        if host in {"localhost", "127.0.0.1", "::1"}:
            return request.url_root.rstrip("/")
    except RuntimeError:
        pass
    return PUBLIC_SITE_URL


def canonical_url(context: dict[str, Any], lang: str | None = None) -> str:
    selected_lang = lang or context["lang"]
    path = f"/{selected_lang}/panchang/{quote(context['slug'], safe='-')}/{context['date'].isoformat()}"
    known = POPULAR_PLACES.get(context["slug"])
    query: dict[str, str] = {}
    if not known or abs(float(known["latitude"]) - context["latitude"]) > 0.01 or abs(float(known["longitude"]) - context["longitude"]) > 0.01:
        query = {
            "place": context["place"],
            "lat": f"{context['latitude']:.6f}",
            "lon": f"{context['longitude']:.6f}",
            "tz": context["timezone"],
        }
        if context.get("country"):
            query["country"] = context["country"]
    return f"{site_root()}{path}" + (f"?{urlencode(query)}" if query else "")


def api_url(context: dict[str, Any]) -> str:
    params = {
        "place": context["place"], "lat": f"{context['latitude']:.6f}", "lon": f"{context['longitude']:.6f}",
        "tz": context["timezone"], "date": context["date"].isoformat(),
        "lang": context["lang"], "live": "1" if context["live"] else "0",
    }
    if not context["live"]:
        params["time"] = context["time"].strftime("%H:%M")
    if context.get("country"):
        params["country"] = context["country"]
    return f"{site_root()}/api/panchang?{urlencode(params)}"


def og_image_url(context: dict[str, Any]) -> str:
    # Keep the language in the path, not only in a query string. Social-media
    # image caches then receive a distinct, extension-bearing resource for
    # every language and minute.
    snapshot = context["at"].strftime("%Y%m%d%H%M")
    params = {
        "place": context["place"], "lat": f"{context['latitude']:.6f}", "lon": f"{context['longitude']:.6f}",
        "tz": context["timezone"], "date": context["date"].isoformat(),
        "time": context["time"].strftime("%H:%M"), "lang": context["lang"], "v": APP_VERSION,
    }
    if context.get("country"):
        params["country"] = context["country"]
    return f"{site_root()}/og/{context['lang']}/{snapshot}.png?{urlencode(params)}"


SEO_COPY_BASE: dict[str, str] = {
    "en": (
        "Use Panchang World for a clear daily Panchang for {place} on {date}. Check {tithi}, {nakshatra}, Yoga, Karana, "
        "sunrise, sunset, Choghadiya, Hora, Muhurta and Lagna with precise local start and end times. The live view updates "
        "every minute for your chosen place, language and timezone. Scroll each timeline to review earlier and upcoming periods, "
        "identify auspicious, mixed and inauspicious windows, and plan worship, travel, meetings, purchases, ceremonies and everyday activities."
    ),
    "hi": (
        "पंचांग वर्ल्ड पर {place} के लिए {date} का स्पष्ट दैनिक पंचांग देखें। {tithi}, {nakshatra}, योग, करण, सूर्योदय, सूर्यास्त, "
        "चौघड़िया, होरा, मुहूर्त और लग्न के सही स्थानीय आरंभ और समाप्ति समय जानें। लाइव दृश्य चुने हुए स्थान, भाषा और समय क्षेत्र के "
        "अनुसार हर मिनट अपडेट होता है। पिछली और आने वाली अवधियाँ देखने, शुभ, मिश्रित और अशुभ समय पहचानने तथा पूजा, यात्रा, बैठक, "
        "खरीदारी, संस्कार और दैनिक कार्यों की योजना बनाने के लिए प्रत्येक टाइमलाइन स्क्रॉल करें।"
    ),
    "mr": (
        "पंचांग वर्ल्डवर {place} साठी {date} चे स्पष्ट दैनिक पंचांग पाहा. {tithi}, {nakshatra}, योग, करण, सूर्योदय, सूर्यास्त, चौघडिया, "
        "होरा, मुहूर्त आणि लग्न यांचे अचूक स्थानिक प्रारंभ व समाप्ती वेळा जाणून घ्या. निवडलेले ठिकाण, भाषा आणि वेळ क्षेत्रानुसार लाइव्ह "
        "दृश्य दर मिनिटाला अद्ययावत होते. मागील व पुढील कालखंड पाहण्यासाठी, शुभ, मिश्र आणि अशुभ वेळ ओळखण्यासाठी तसेच पूजा, प्रवास, "
        "बैठक, खरेदी, संस्कार आणि दैनंदिन कामांचे नियोजन करण्यासाठी प्रत्येक टाइमलाइन स्क्रोल करा."
    ),
    "gu": (
        "પંચાંગ વર્લ્ડ પર {place} માટે {date} નું સ્પષ્ટ દૈનિક પંચાંગ જુઓ. {tithi}, {nakshatra}, યોગ, કરણ, સૂર્યોદય, સૂર્યાસ્ત, ચોઘડિયા, "
        "હોરા, મુહૂર્ત અને લગ્નના ચોક્કસ સ્થાનિક આરંભ અને અંત સમય જાણો. પસંદ કરેલા સ્થળ, ભાષા અને સમય ક્ષેત્ર મુજબ લાઇવ દૃશ્ય દર મિનિટે "
        "અપડેટ થાય છે. અગાઉના અને આગામી સમયખંડ જોવા, શુભ, મિશ્ર અને અશુભ સમય ઓળખવા તથા પૂજા, પ્રવાસ, બેઠક, ખરીદી, સંસ્કાર અને દૈનિક "
        "કાર્યોનું આયોજન કરવા દરેક સમયરેખા સ્ક્રોલ કરો."
    ),
    "bn": (
        "পঞ্চাঙ্গ ওয়ার্ল্ডে {place} এলাকার {date} তারিখের পরিষ্কার দৈনিক পঞ্জিকা দেখুন। {tithi}, {nakshatra}, যোগ, করণ, সূর্যোদয়, সূর্যাস্ত, "
        "চৌঘড়িয়া, হোরা, মুহূর্ত ও লগ্নের সঠিক স্থানীয় শুরু এবং শেষ সময় জানুন। নির্বাচিত স্থান, ভাষা ও সময় অঞ্চলের ভিত্তিতে লাইভ দৃশ্য প্রতি "
        "মিনিটে হালনাগাদ হয়। আগের ও পরের সময়কাল দেখতে, শুভ, মিশ্র ও অশুভ সময় বুঝতে এবং পূজা, ভ্রমণ, সভা, কেনাকাটা, সংস্কার ও দৈনন্দিন "
        "কাজ পরিকল্পনা করতে প্রতিটি টাইমলাইন স্ক্রল করুন।"
    ),
    "ta": (
        "பஞ்சாங்க் வேர்ல்டில் {place} இடத்திற்கான {date} தேதியின் தெளிவான தினசரி பஞ்சாங்கத்தைப் பாருங்கள். {tithi}, {nakshatra}, யோகம், கரணம், "
        "சூரியோதயம், சூரியாஸ்தமனம், சோகடியா, ஹோரா, முகூர்த்தம் மற்றும் லக்னத்தின் துல்லியமான உள்ளூர் தொடக்கம் மற்றும் முடிவு நேரங்களை அறியுங்கள். "
        "தேர்ந்த இடம், மொழி, நேர மண்டலத்துக்கு ஏற்ப நேரடி காட்சி ஒவ்வொரு நிமிடமும் புதுப்பிக்கப்படும். முந்தைய மற்றும் வரவிருக்கும் காலங்களைப் பார்க்கவும், "
        "சுப, கலப்பு, அசுப நேரங்களை அறிந்து பூஜை, பயணம், கூட்டம், கொள்முதல், சடங்கு மற்றும் தினசரி பணிகளைத் திட்டமிடவும் ஒவ்வொரு காலவரிசையையும் நகர்த்துங்கள்."
    ),
    "te": (
        "పంచాంగ్ వరల్డ్‌లో {place} కోసం {date} తేదీకి స్పష్టమైన రోజువారీ పంచాంగాన్ని చూడండి. {tithi}, {nakshatra}, యోగం, కరణం, సూర్యోదయం, సూర్యాస్తమయం, "
        "చౌఘడియా, హోరా, ముహూర్తం మరియు లగ్నం యొక్క ఖచ్చితమైన స్థానిక ప్రారంభం, ముగింపు సమయాలను తెలుసుకోండి. ఎంచుకున్న ప్రదేశం, భాష, సమయ మండలానికి "
        "అనుగుణంగా లైవ్ దృశ్యం ప్రతి నిమిషం నవీకరించబడుతుంది. గత మరియు రాబోయే కాలాలను చూడటానికి, శుభ, మిశ్రమ, అశుభ సమయాలను గుర్తించి పూజ, ప్రయాణం, "
        "సమావేశం, కొనుగోలు, సంస్కారం మరియు రోజువారీ పనులను ప్లాన్ చేయటానికి ప్రతి టైమ్‌లైన్‌ను స్క్రోల్ చేయండి."
    ),
    "kn": (
        "ಪಂಚಾಂಗ್ ವರ್ಲ್ಡ್‌ನಲ್ಲಿ {place} ಸ್ಥಳದ {date} ದಿನದ ಸ್ಪಷ್ಟ ದೈನಂದಿನ ಪಂಚಾಂಗವನ್ನು ನೋಡಿ. {tithi}, {nakshatra}, ಯೋಗ, ಕರಣ, ಸೂರ್ಯೋದಯ, ಸೂರ್ಯಾಸ್ತ, "
        "ಚೌಘಡಿಯಾ, ಹೋರಾ, ಮುಹೂರ್ತ ಮತ್ತು ಲಗ್ನದ ನಿಖರ ಸ್ಥಳೀಯ ಆರಂಭ ಹಾಗೂ ಅಂತ್ಯ ಸಮಯಗಳನ್ನು ತಿಳಿಯಿರಿ. ಆಯ್ದ ಸ್ಥಳ, ಭಾಷೆ ಮತ್ತು ಸಮಯ ವಲಯಕ್ಕೆ ಅನುಗುಣವಾಗಿ ಲೈವ್ "
        "ನೋಟವು ಪ್ರತಿ ನಿಮಿಷ ನವೀಕರಿಸುತ್ತದೆ. ಹಿಂದಿನ ಮತ್ತು ಮುಂದಿನ ಅವಧಿಗಳನ್ನು ನೋಡಲು, ಶುಭ, ಮಿಶ್ರ ಮತ್ತು ಅಶುಭ ಸಮಯಗಳನ್ನು ಗುರುತಿಸಲು ಹಾಗೂ ಪೂಜೆ, ಪ್ರಯಾಣ, ಸಭೆ, "
        "ಖರೀದಿ, ಸಂಸ್ಕಾರ ಮತ್ತು ದಿನನಿತ್ಯದ ಕೆಲಸಗಳನ್ನು ಯೋಜಿಸಲು ಪ್ರತಿಯೊಂದು ಸಮಯರೇಖೆಯನ್ನು ಸ್ಕ್ರೋಲ್ ಮಾಡಿ."
    ),
    "ml": (
        "പഞ്ചാങ് വേൾഡിൽ {place} സ്ഥലത്തിനുള്ള {date} തീയതിയിലെ വ്യക്തമായ ദിവസപ്പഞ്ചാംഗം കാണുക. {tithi}, {nakshatra}, യോഗം, കരണം, സൂര്യോദയം, സൂര്യാസ്തമയം, "
        "ചൗഘഡിയ, ഹോര, മുഹൂർത്തം, ലഗ്നം എന്നിവയുടെ കൃത്യമായ പ്രാദേശിക ആരംഭവും അവസാനവും അറിയുക. തിരഞ്ഞെടുത്ത സ്ഥലം, ഭാഷ, സമയമേഖല അനുസരിച്ച് ലൈവ് കാഴ്ച "
        "ഓരോ മിനിറ്റിലും പുതുക്കുന്നു. കഴിഞ്ഞതും വരാനിരിക്കുന്നതുമായ കാലങ്ങൾ കാണാനും ശുഭ, മിശ്ര, അശുഭ സമയങ്ങൾ തിരിച്ചറിയാനും പൂജ, യാത്ര, യോഗം, വാങ്ങൽ, സംസ്കാരം, "
        "ദൈനംദിന പ്രവർത്തനങ്ങൾ എന്നിവ ആസൂത്രണം ചെയ്യാനും ഓരോ സമയരേഖയും സ്ക്രോൾ ചെയ്യുക."
    ),
    "pa": (
        "ਪੰਚਾਂਗ ਵਰਲਡ ਉੱਤੇ {place} ਲਈ {date} ਦਾ ਸਾਫ਼ ਰੋਜ਼ਾਨਾ ਪੰਚਾਂਗ ਵੇਖੋ। {tithi}, {nakshatra}, ਯੋਗ, ਕਰਣ, ਸੂਰਜ ਚੜ੍ਹਨਾ, ਸੂਰਜ ਡੁੱਬਣਾ, ਚੌਘੜੀਆ, "
        "ਹੋਰਾ, ਮੁਹੂਰਤ ਅਤੇ ਲਗਨ ਦੇ ਸਹੀ ਸਥਾਨਕ ਸ਼ੁਰੂ ਅਤੇ ਅੰਤ ਸਮੇਂ ਜਾਣੋ। ਚੁਣੇ ਹੋਏ ਸਥਾਨ, ਭਾਸ਼ਾ ਅਤੇ ਸਮਾਂ ਖੇਤਰ ਅਨੁਸਾਰ ਲਾਈਵ ਦ੍ਰਿਸ਼ ਹਰ ਮਿੰਟ ਅੱਪਡੇਟ "
        "ਹੁੰਦਾ ਹੈ। ਪਿਛਲੇ ਅਤੇ ਆਉਣ ਵਾਲੇ ਸਮੇਂ ਵੇਖਣ, ਸ਼ੁਭ, ਮਿਲੇ-ਜੁਲੇ ਅਤੇ ਅਸ਼ੁਭ ਵੇਲੇ ਪਛਾਣਣ ਅਤੇ ਪੂਜਾ, ਯਾਤਰਾ, ਮੀਟਿੰਗ, ਖਰੀਦਦਾਰੀ, ਸੰਸਕਾਰ ਤੇ ਰੋਜ਼ਾਨਾ ਕੰਮਾਂ "
        "ਦੀ ਯੋਜਨਾ ਬਣਾਉਣ ਲਈ ਹਰ ਟਾਈਮਲਾਈਨ ਸਕ੍ਰੋਲ ਕਰੋ।"
    ),
    "or": (
        "ପଞ୍ଚାଙ୍ଗ ୱର୍ଲ୍ଡରେ {place} ପାଇଁ {date} ତାରିଖର ସ୍ପଷ୍ଟ ଦୈନିକ ପଞ୍ଚାଙ୍ଗ ଦେଖନ୍ତୁ। {tithi}, {nakshatra}, ଯୋଗ, କରଣ, ସୂର୍ଯ୍ୟୋଦୟ, ସୂର୍ଯ୍ୟାସ୍ତ, "
        "ଚୌଘଡ଼ିଆ, ହୋରା, ମୁହୂର୍ତ୍ତ ଏବଂ ଲଗ୍ନର ସଠିକ୍ ସ୍ଥାନୀୟ ଆରମ୍ଭ ଓ ଶେଷ ସମୟ ଜାଣନ୍ତୁ। ଚୟନିତ ସ୍ଥାନ, ଭାଷା ଓ ସମୟ ମଣ୍ଡଳ ଅନୁସାରେ ଲାଇଭ୍ "
        "ଦୃଶ୍ୟ ପ୍ରତି ମିନିଟରେ ଅଦ୍ୟତନ ହୁଏ। ପୂର୍ବ ଓ ଆଗାମୀ ସମୟ ଦେଖିବା, ଶୁଭ, ମିଶ୍ର ଓ ଅଶୁଭ ସମୟ ଚିହ୍ନିବା ଏବଂ ପୂଜା, ଯାତ୍ରା, ବୈଠକ, କ୍ରୟ, "
        "ସଂସ୍କାର ଓ ଦୈନିକ କାମ ଯୋଜନା କରିବା ପାଇଁ ପ୍ରତ୍ୟେକ ସମୟରେଖା ସ୍କ୍ରୋଲ୍ କରନ୍ତୁ।"
    ),
    "ne": (
        "पञ्चाङ्ग वर्ल्डमा {place} का लागि {date} को स्पष्ट दैनिक पञ्चाङ्ग हेर्नुहोस्। {tithi}, {nakshatra}, योग, करण, सूर्योदय, सूर्यास्त, चौघडिया, होरा, "
        "मुहूर्त र लग्नका सही स्थानीय सुरु र अन्त्य समय जान्नुहोस्। रोजिएको स्थान, भाषा र समय क्षेत्रअनुसार लाइभ दृश्य हरेक मिनेट अद्यावधिक हुन्छ। अघिल्ला र "
        "आगामी अवधिहरू हेर्न, शुभ, मिश्रित र अशुभ समय पहिचान गर्न तथा पूजा, यात्रा, बैठक, खरिद, संस्कार र दैनिक कामको योजना बनाउन प्रत्येक समयरेखा स्क्रोल "
        "गर्नुहोस्। पृष्ठ सुरक्षित गर्नुहोस् र बिहानको सूचना चालु गरेर दिनभर भरपर्दो पात्रो मार्गदर्शनका लागि फर्कनुहोस्।"
    ),
    "sa": (
        "पञ्चाङ्ग वर्ल्ड मध्ये {place} स्थानस्य {date} दिनाङ्कस्य स्पष्टं दैनिकं पञ्चाङ्गं पश्यतु। {tithi}, {nakshatra}, योगः, करणम्, सूर्योदयः, सूर्यास्तः, चौघडिया, "
        "होरा, मुहूर्तः, लग्नं च यथार्थस्थानीयारम्भसमाप्तिसमयैः ज्ञायताम्। चयनितस्थानभाषाकालक्षेत्रानुसारं जीवदृश्यं प्रतिनिमेषम् अद्यतनं भवति। पूर्वागामिकालान् द्रष्टुं, "
        "शुभमिश्राशुभसमयान् ज्ञातुं, पूजायात्रासभाक्रयसंस्कारदैनिककार्याणां योजनां कर्तुं प्रत्येकां कालरेखां सञ्चालयतु। पृष्ठं रक्षतु, प्रातःसूचनां सक्रियीकुरुतु, दिवसभरं पठनीयाय "
        "विश्वसनीयाय च हिन्दूपञ्चाङ्गमार्गदर्शनाय पुनरागच्छतु।"
    ),
}


def build_seo_copy(context: dict[str, Any], data: dict[str, Any]) -> str:
    """Return exactly 100 visible, localized SEO words without altering the meta description."""
    lang = context["lang"]
    summary = data.get("summary", {})
    base = SEO_COPY_BASE.get(lang, SEO_COPY_BASE["en"]).format(
        place=context["place"],
        date=format_date_label(context["date"], lang),
        tithi=summary.get("tithi", {}).get("title", tr(lang, "tithi")),
        nakshatra=summary.get("nakshatra", {}).get("title", tr(lang, "nakshatra")),
    ).strip()
    words = base.split()
    related_phrases: list[str] = [
        tr(lang, "panchang"), tr(lang, "tithi"), tr(lang, "nakshatra"), tr(lang, "yoga"),
        tr(lang, "karana"), tr(lang, "sunrise"), tr(lang, "sunset"), tr(lang, "choghadiya"),
        tr(lang, "hora"), tr(lang, "period"), tr(lang, "lagna"), tr(lang, "good"),
        tr(lang, "avoid"), tr(lang, "today"), context["place"], format_date_label(context["date"], lang),
        "Panchang", "Panchangam", "Tithi", "Nakshatra", "Yoga", "Karana", "Choghadiya", "Hora",
        "Muhurta", "Lagna", "Rahu", "Kalam", "Brahma", "Abhijit", "Sunrise", "Sunset",
    ]
    related_phrases.extend(localize_sanskrit(pair, lang) for pair in NAKSHATRA_NAMES)
    related_phrases.extend(localize_sanskrit(pair, lang) for pair in TITHI_NAMES)
    seen = {re.sub(r"[^\w\u0080-\uffff]+", "", word, flags=re.UNICODE).casefold() for word in words}
    extras: list[str] = []
    for phrase in related_phrases:
        for token in str(phrase).split():
            clean = re.sub(r"[^\w\u0080-\uffff]+", "", token, flags=re.UNICODE).casefold()
            if clean and clean not in seen:
                seen.add(clean)
                extras.append(token.strip(" ,.;:—–"))
    if len(words) < 100:
        needed = 100 - len(words)
        words.extend(extras[:needed])
    if len(words) < 100:
        fallback = ["daily", "calendar", "timings", "local", "today", "auspicious", "muhurta"]
        index = 0
        while len(words) < 100:
            words.append(fallback[index % len(fallback)])
            index += 1
    return " ".join(words[:100]).rstrip(" ,.;:—–") + "."


def build_seo_keywords(context: dict[str, Any], data: dict[str, Any]) -> str:
    # The visible copy carries the substance; this concise metadata list helps
    # non-Google consumers without replacing or lengthening the description.
    terms = [
        tr(context["lang"], "panchang"), context["place"], format_date_label(context["date"], context["lang"]),
        tr(context["lang"], "tithi"), tr(context["lang"], "nakshatra"), tr(context["lang"], "yoga"),
        tr(context["lang"], "karana"), tr(context["lang"], "choghadiya"), tr(context["lang"], "hora"),
        tr(context["lang"], "period"), tr(context["lang"], "lagna"), "Panchang", "Panchangam",
    ]
    return ", ".join(dict.fromkeys(str(term).strip() for term in terms if str(term).strip()))


def seo_payload(context: dict[str, Any], data: dict[str, Any]) -> dict[str, Any]:
    lang = context["lang"]
    summary = data["summary"]
    date_english = format_date_label(context["date"], "en")
    date_local = format_date_label(context["date"], lang)
    tithi = summary.get("tithi", {}).get("title", tr(lang, "tithi"))
    nakshatra = summary.get("nakshatra", {}).get("title", tr(lang, "nakshatra"))
    yoga = summary.get("yoga", {}).get("title", tr(lang, "yoga"))
    sunrise = summary.get("sunrise", {}).get("time", "")
    sunset = summary.get("sunset", {}).get("time", "")
    if lang == "en":
        title = f"Panchang for {context['place']} on {date_english} – {tithi}, {nakshatra}"
        description = (
            f"Local {date_english} Panchang for {context['place']}: {tithi} Tithi, {nakshatra} Nakshatra, "
            f"{yoga} Yoga, sunrise {sunrise}, sunset {sunset}, live Choghadiya, Hora, Muhurta and Lagna timings."
        )
    else:
        title = f"{tr(lang, 'panchang')} – {context['place']} – {date_local} – {tithi}, {nakshatra}"
        description = (
            f"{tr(lang, 'panchang')} — {context['place']}, {date_local}. "
            f"{tr(lang, 'tithi')}: {tithi}; {tr(lang, 'nakshatra')}: {nakshatra}; {tr(lang, 'yoga')}: {yoga}; "
            f"{tr(lang, 'sunrise')}: {sunrise}; {tr(lang, 'sunset')}: {sunset}; "
            f"{tr(lang, 'choghadiya')}, {tr(lang, 'hora')}, {tr(lang, 'period')}, {tr(lang, 'lagna')}."
        )
    canonical = canonical_url(context)
    alternates = {code: canonical_url(context, code) for code in LANGUAGES}
    alternates["x-default"] = canonical_url(context, "en")
    image_alt = f"{tr(lang, 'share_image_alt')}: {context['place']}, {date_local}"
    seo_copy = build_seo_copy(context, data)
    return {
        "title": title[:200], "description": description[:320], "canonical": canonical,
        "alternates": alternates, "og_image": og_image_url(context), "image_alt": image_alt[:220],
        "copy": seo_copy, "keywords": build_seo_keywords(context, data),
    }


def build_jsonld(context: dict[str, Any], data: dict[str, Any], seo: dict[str, Any]) -> dict[str, Any]:
    """Build accurate, page-visible Schema.org entities.

    The graph intentionally avoids unrelated rich-result types. Every entity
    describes either this visible Panchang, its downloadable data, the web app,
    or the public API that produces the values.
    """
    root = site_root()
    place_id = f"{seo['canonical']}#place"
    dataset_id = f"{seo['canonical']}#dataset"
    page_id = f"{seo['canonical']}#webpage"
    image_id = f"{seo['canonical']}#primaryimage"
    item_list_id = f"{seo['canonical']}#panchang-items"
    terms_id = f"{root}#panchang-terms"
    app_id = f"{root}#webapp"
    api_id = f"{root}#api"
    catalog_id = f"{root}#data-catalog"
    website_id = f"{root}#website"
    publisher_id = f"{root}#publisher"

    language_entities = [
        {"@type": "Language", "name": info["name"], "alternateName": code}
        for code, info in LANGUAGES.items()
    ]
    social_image = {
        "@type": "ImageObject",
        "@id": image_id,
        "url": seo["og_image"],
        "contentUrl": seo["og_image"],
        "encodingFormat": "image/png",
        "width": 1200,
        "height": 630,
        "caption": seo["title"],
        "representativeOfPage": True,
        "inLanguage": context["lang"],
    }

    observations: list[dict[str, Any]] = []
    variables: list[dict[str, Any]] = []
    item_list: list[dict[str, Any]] = []
    defined_terms: list[dict[str, Any]] = []

    for position, section in enumerate(data["sections"], start=1):
        item = current_or_focused(section["items"])
        if not item:
            continue
        variable_id = f"{terms_id}/{section['key']}"
        defined_terms.append({
            "@type": "DefinedTerm",
            "@id": variable_id,
            "name": section["label"],
            "termCode": section["key"],
            "description": f"{section['label']} value and timing in the local Panchang.",
            "inDefinedTermSet": {"@id": terms_id},
        })
        variables.append({
            "@type": "PropertyValue",
            "name": section["label"],
            "value": item.get("title", ""),
            "description": item.get("time", ""),
            "propertyID": variable_id,
            "measurementTechnique": data["method"],
        })
        additional_properties: list[dict[str, Any]] = [
            {"@type": "PropertyValue", "name": "Display date", "value": item.get("date", "")},
            {"@type": "PropertyValue", "name": "Display time", "value": item.get("clock", "")},
            {"@type": "PropertyValue", "name": "Display timing", "value": item.get("time", "")},
            {"@type": "PropertyValue", "name": "Classification", "value": item.get("quality", "neutral")},
            {"@type": "PropertyValue", "name": "Timezone", "value": context["timezone"]},
        ]
        if item.get("start"):
            additional_properties.append({"@type": "PropertyValue", "name": "Start", "value": item["start"]})
        if item.get("end"):
            additional_properties.append({"@type": "PropertyValue", "name": "End", "value": item["end"]})
        observation = {
            "@type": "Observation",
            "@id": f"{seo['canonical']}#observation-{section['key']}",
            "name": f"{section['label']} for {context['place']}",
            "description": f"{item.get('title', '')}: {item.get('time', '')}",
            "observationAbout": {"@id": place_id},
            "observationDate": context["at"].isoformat(),
            "variableMeasured": section["label"],
            "value": item.get("title", ""),
            "measurementTechnique": data["method"],
            "additionalProperty": additional_properties,
            "isPartOf": {"@id": dataset_id},
        }
        observations.append(observation)
        item_list.append({
            "@type": "ListItem",
            "position": position,
            "item": {"@id": observation["@id"]},
            "name": section["label"],
            "description": f"{item.get('title', '')}: {item.get('time', '')}",
        })

    place = {
        "@type": "Place",
        "@id": place_id,
        "name": context["place"],
        "geo": {
            "@type": "GeoCoordinates",
            "latitude": context["latitude"],
            "longitude": context["longitude"],
        },
        "additionalProperty": {"@type": "PropertyValue", "name": "IANA timezone", "value": context["timezone"]},
    }
    if context.get("country"):
        place["address"] = {
            "@type": "PostalAddress",
            "addressLocality": context["place"],
            "addressCountry": context["country"],
        }

    graph: list[dict[str, Any]] = [
        {
            "@type": "Organization",
            "@id": publisher_id,
            "name": APP_NAME,
            "url": root,
            "logo": {"@type": "ImageObject", "url": f"{root}/icon-512.png", "width": 512, "height": 512},
        },
        social_image,
        {
            "@type": "WebSite",
            "@id": website_id,
            "url": root,
            "name": APP_NAME,
            "description": "Live, location-aware Hindu Panchang timelines.",
            "inLanguage": list(LANGUAGES.keys()),
            "availableLanguage": language_entities,
            "publisher": {"@id": publisher_id},
            "image": {"@id": image_id},
            "potentialAction": {
                "@type": "SearchAction",
                "target": {"@type": "EntryPoint", "urlTemplate": f"{root}/search?place={{search_term_string}}"},
                "query-input": "required name=search_term_string",
            },
        },
        {
            "@type": "WebApplication",
            "@id": app_id,
            "name": APP_NAME,
            "url": root,
            "description": seo["description"],
            "applicationCategory": "LifestyleApplication",
            "applicationSubCategory": "Hindu Panchang and Vedic calendar",
            "operatingSystem": "Any",
            "browserRequirements": "A modern web browser; core Panchang content is server-rendered.",
            "softwareVersion": APP_VERSION,
            "isAccessibleForFree": True,
            "availableLanguage": language_entities,
            "countriesSupported": "Worldwide",
            "image": {"@id": image_id},
            "screenshot": {"@id": image_id},
            "offers": {"@type": "Offer", "price": "0", "priceCurrency": "USD"},
            "featureList": [
                "Location-aware Panchang",
                "Tithi timeline",
                "Nakshatra timeline",
                "Yoga and Karana timelines",
                "Local sunrise and sunset",
                "Live Choghadiya and Hora",
                "Muhurta overlays",
                "Current Lagna",
                "Multiple Indian languages",
                "Installable mobile web application",
            ],
            "publisher": {"@id": publisher_id},
            "potentialAction": {"@type": "ViewAction", "target": seo["canonical"]},
        },
        {
            "@type": "WebAPI",
            "@id": api_id,
            "name": f"{APP_NAME} JSON API",
            "url": f"{root}/api/panchang",
            "description": "Machine-readable live Panchang timelines for a selected place and date.",
            "documentation": f"{root}/openapi.json",
            "serviceType": "Panchang calculation API",
            "provider": {"@id": publisher_id},
            "areaServed": "Worldwide",
            "availableLanguage": language_entities,
            "isAccessibleForFree": True,
            "serviceOutput": {"@id": dataset_id},
        },
        {
            "@type": "DataCatalog",
            "@id": catalog_id,
            "name": f"{APP_NAME} data catalog",
            "description": "Location and date-specific Panchang datasets available through the website and JSON API.",
            "url": f"{root}/openapi.json",
            "publisher": {"@id": publisher_id},
            "dataset": {"@id": dataset_id},
            "measurementTechnique": data["method"],
        },
        {
            "@type": "WebPage",
            "@id": page_id,
            "url": seo["canonical"],
            "name": seo["title"],
            "headline": seo["title"],
            "description": seo["description"],
            "text": seo["copy"],
            "keywords": seo["keywords"],
            "inLanguage": context["lang"],
            "isPartOf": {"@id": website_id},
            "about": [{"@id": place_id}, {"@id": terms_id}],
            "contentLocation": {"@id": place_id},
            "associatedMedia": {"@id": image_id},
            "mainEntity": {"@id": dataset_id},
            "dateModified": data["generated_at"],
            "isAccessibleForFree": True,
            "primaryImageOfPage": {"@id": image_id},
            "thumbnailUrl": seo["og_image"],
            "speakable": {"@type": "SpeakableSpecification", "cssSelector": ["#currentHeaderText", ".metric-row"]},
            "breadcrumb": {"@id": f"{seo['canonical']}#breadcrumb"},
            "potentialAction": [
                {"@type": "ViewAction", "target": seo["canonical"], "name": f"View Panchang for {context['place']}"},
                {"@type": "ReadAction", "target": seo["canonical"]},
            ],
        },
        {
            "@type": "Dataset",
            "@id": dataset_id,
            "name": seo["title"],
            "description": seo["description"],
            "abstract": seo["copy"],
            "url": seo["canonical"],
            "mainEntityOfPage": {"@id": page_id},
            "creator": {"@id": app_id},
            "publisher": {"@id": publisher_id},
            "includedInDataCatalog": {"@id": catalog_id},
            "dateModified": data["generated_at"],
            "inLanguage": context["lang"],
            "isAccessibleForFree": True,
            "image": {"@id": image_id},
            "temporalCoverage": context["date"].isoformat(),
            "spatialCoverage": {"@id": place_id},
            "measurementTechnique": data["method"],
            "variableMeasured": variables,
            "distribution": {
                "@type": "DataDownload",
                "contentUrl": api_url(context),
                "encodingFormat": "application/json",
                "name": "Machine-readable Panchang JSON",
            },
            "keywords": [
                seo["keywords"], "Panchang", "Panchangam", "Tithi", "Nakshatra", "Yoga", "Karana", "Choghadiya", "Hora",
                "Muhurta", "Lagna", context["place"], format_date_label(context["date"], context["lang"]),
            ],
            "hasPart": [{"@id": observation["@id"]} for observation in observations],
        },
        {
            "@type": "DefinedTermSet",
            "@id": terms_id,
            "name": "Panchang elements",
            "description": "The calendrical and time-period elements displayed by this Panchang.",
            "about": {"@id": dataset_id},
            "hasDefinedTerm": [{"@id": term["@id"]} for term in defined_terms],
        },
        *defined_terms,
        place,
        *observations,
        {
            "@type": "ItemList",
            "@id": item_list_id,
            "name": "Current Panchang elements",
            "numberOfItems": len(item_list),
            "itemListElement": item_list,
        },
        {
            "@type": "BreadcrumbList",
            "@id": f"{seo['canonical']}#breadcrumb",
            "itemListElement": [
                {"@type": "ListItem", "position": 1, "name": APP_NAME, "item": root},
                {"@type": "ListItem", "position": 2, "name": context["place"], "item": f"{root}/{context['lang']}/panchang/{quote(context['slug'], safe='-')}"},
                {"@type": "ListItem", "position": 3, "name": context["date"].isoformat(), "item": seo["canonical"]},
            ],
        },
    ]
    return {"@context": "https://schema.org", "@graph": graph}

def safe_script_json(value: Any) -> str:
    return (
        json.dumps(value, ensure_ascii=False, separators=(",", ":"))
        .replace("<", "\\u003c")
        .replace(">", "\\u003e")
        .replace("&", "\\u0026")
        .replace("\u2028", "\\u2028")
        .replace("\u2029", "\\u2029")
    )

# ---------------------------------------------------------------------------
# Embedded presentation layer
# ---------------------------------------------------------------------------

CSS = r"""
:root {
  color-scheme: light;
  --bg: #f2f5f5;
  --bg-soft: #ffffff;
  --surface: rgba(255, 255, 255, .94);
  --surface-strong: #ffffff;
  --surface-muted: #f2f5f7;
  --rail-bg: rgba(255, 255, 255, .87);
  --line: rgba(32, 43, 54, .12);
  --line-strong: rgba(32, 43, 54, .22);
  --text: #171920;
  --muted: #626c79;
  --gold: #d99500;
  --gold-soft: #fff0b8;
  --cyan: #178f9c;
  --mint: #118d78;
  --rose: #d24869;
  --lavender: #6862dc;
  --peach: #ef6e58;
  --good: #07816d;
  --good-bg: #dff3e9;
  --bad: #c93f5e;
  --bad-bg: #fbe4ea;
  --neutral-bg: #f1f4f6;
  --shadow: 0 13px 34px rgba(31, 48, 58, .11);
  --radius: clamp(10px, 1.45vmin, 16px);
  --gap: clamp(3px, .55vh, 7px);
  --pad: clamp(4px, .75vmin, 9px);
  --header-height: clamp(58px, 8.25vh, 82px);
  --label-width: clamp(118px, 20vw, 290px);
  --header-left-space: clamp(49px, 5.6vw, 64px);
  --header-right-space: clamp(49px, 5.6vw, 64px);
  --dialog-backdrop: rgba(23, 33, 40, .43);
}

html[data-theme="dark"] {
  color-scheme: dark;
  --bg: #061923;
  --bg-soft: #0b2130;
  --surface: rgba(13, 35, 49, .97);
  --surface-strong: #102b3b;
  --surface-muted: #142b3a;
  --rail-bg: rgba(8, 25, 36, .94);
  --line: rgba(218, 234, 241, .14);
  --line-strong: rgba(218, 234, 241, .26);
  --text: #fbfdff;
  --muted: #c7d3dc;
  --gold: #f0b64b;
  --gold-soft: #5b471d;
  --cyan: #55d0dc;
  --mint: #57d5ad;
  --rose: #fa8293;
  --lavender: #aaa6ff;
  --peach: #ff9c88;
  --good: #5bd8b3;
  --good-bg: #0d493d;
  --bad: #ff8aa0;
  --bad-bg: #552835;
  --neutral-bg: #172b3a;
  --shadow: 0 18px 45px rgba(0, 0, 0, .32);
  --dialog-backdrop: rgba(0, 8, 13, .72);
}

* { box-sizing: border-box; }
html, body { width: 100%; height: 100%; margin: 0; overflow: hidden; overscroll-behavior: none; }
html { background: var(--bg); }
body {
  min-height: 100dvh;
  color: var(--text);
  background:
    radial-gradient(60vmax 40vmax at -8% -18%, rgba(255, 218, 117, .28), transparent 58%),
    radial-gradient(55vmax 44vmax at 108% 0%, rgba(83, 203, 211, .20), transparent 60%),
    linear-gradient(145deg, var(--bg-soft), var(--bg));
  font-family: Inter, ui-sans-serif, system-ui, -apple-system, BlinkMacSystemFont, "Segoe UI", "Noto Sans",
    "Noto Sans Devanagari", "Noto Sans Gujarati", "Noto Sans Bengali", "Noto Sans Tamil",
    "Noto Sans Telugu", "Noto Sans Kannada", "Noto Sans Malayalam", "Noto Sans Gurmukhi",
    "Noto Sans Oriya", "Noto Sans Odia", "Nirmala UI", sans-serif;
  -webkit-font-smoothing: antialiased;
  text-rendering: optimizeLegibility;
}
html[data-theme="dark"] body {
  background:
    radial-gradient(65vmax 45vmax at -8% -18%, rgba(240, 182, 75, .15), transparent 58%),
    radial-gradient(55vmax 44vmax at 108% 0%, rgba(85, 208, 220, .13), transparent 60%),
    linear-gradient(145deg, #061923, #0a2636 58%, #071823);
}
button, input, select { font: inherit; }
button { -webkit-tap-highlight-color: transparent; }

.ambient { position: fixed; inset: 0; pointer-events: none; overflow: hidden; z-index: 0; }
.ambient::before, .ambient::after { content: ""; position: absolute; border-radius: 50%; opacity: .62; }
.ambient::before {
  width: 42vmax; height: 42vmax; left: -27vmax; top: 20%;
  border: 1px solid rgba(222, 160, 21, .13); box-shadow: 0 0 80px rgba(222, 160, 21, .05) inset;
}
.ambient::after {
  width: 34vmax; height: 34vmax; right: -22vmax; top: 9%;
  border: 1px solid rgba(23, 143, 156, .12); box-shadow: 0 0 80px rgba(23, 143, 156, .04) inset;
}

.app-shell {
  position: relative; z-index: 1; width: 100%; height: 100dvh; max-width: 1920px; margin: 0 auto;
  padding: var(--pad); display: grid; grid-template-rows: var(--header-height) minmax(0, 1fr);
  gap: var(--gap); isolation: isolate;
}

.day-carousel {
  min-width: 0; min-height: 0; overflow: hidden; border: 1px solid rgba(55, 112, 119, .18);
  border-radius: var(--radius); position: relative;
  background: linear-gradient(108deg, #fff2bd 0%, #fffaf0 25%, #f6faf9 55%, #dff4f4 100%);
  box-shadow: var(--shadow), inset 0 1px 0 rgba(255,255,255,.78);
}
html[data-theme="dark"] .day-carousel {
  border-color: rgba(85, 208, 220, .24);
  background: linear-gradient(108deg, rgba(88, 69, 28, .82), rgba(20, 48, 60, .96) 34%, rgba(8, 37, 52, .98) 72%, rgba(34, 92, 100, .70));
  box-shadow: var(--shadow), inset 0 1px 0 rgba(255,255,255,.04);
}
.day-carousel::before {
  content: ""; position: absolute; inset: 0; pointer-events: none;
  background: radial-gradient(30% 130% at 0 50%, rgba(255, 222, 133, .17), transparent 72%),
              radial-gradient(30% 130% at 100% 50%, rgba(59, 183, 192, .11), transparent 72%);
}
.day-rail {
  position: relative; z-index: 1; display: flex; width: 100%; height: 100%; overflow-x: auto; overflow-y: hidden;
  scroll-snap-type: x mandatory; scrollbar-width: none; overscroll-behavior-x: contain; touch-action: pan-x;
}
.day-rail::-webkit-scrollbar, .timeline::-webkit-scrollbar { display: none; }
.day-panel {
  flex: 0 0 100%; width: 100%; min-width: 0; height: 100%; scroll-snap-align: center; scroll-snap-stop: always;
  display: grid; place-items: center; overflow: hidden;
  padding: 0 calc(var(--header-right-space) + 7px) 0 calc(var(--header-left-space) + 7px);
}
.day-title {
  display: block; width: 100%; margin: 0; white-space: nowrap; text-align: center; overflow: hidden; text-overflow: clip;
  color: var(--text); font-size: clamp(18px, 2.55vw, 41px); line-height: 1.16; padding-block: .08em; font-weight: 900; letter-spacing: -.045em;
  font-variant-numeric: tabular-nums;
}
.header-compact { display: none; }
.day-panel[data-position="previous"] .day-title,
.day-panel[data-position="next"] .day-title { color: var(--muted); }

.header-control {
  min-width: 44px; min-height: 44px; border: 1px solid rgba(202, 151, 36, .34); border-radius: 999px;
  display: grid; place-items: center; color: #9b6800; background: rgba(255,255,255,.82); cursor: pointer;
  box-shadow: 0 6px 17px rgba(43, 53, 58, .10), inset 0 1px 0 rgba(255,255,255,.86);
  transition: transform .16s ease, background .16s ease, border-color .16s ease, box-shadow .16s ease, opacity .16s ease;
  backdrop-filter: blur(8px);
}
html[data-theme="dark"] .header-control {
  color: #ffd572; border-color: rgba(240,182,75,.26); background: rgba(45, 44, 30, .70);
  box-shadow: 0 8px 22px rgba(0,0,0,.24), inset 0 1px 0 rgba(255,255,255,.04);
}
.header-control:hover { transform: translateY(-1px); border-color: rgba(211,151,15,.62); background: #fff; }
html[data-theme="dark"] .header-control:hover { background: rgba(88, 69, 28, .82); }
.header-control:active { transform: translateY(1px) scale(.97); }
.header-control:disabled { opacity: .55; cursor: wait; }
.previous-control {
  position: absolute; z-index: 5; left: clamp(6px, .8vw, 12px); top: 50%; transform: translateY(-50%);
  width: clamp(42px, 5.2vmin, 50px); height: clamp(42px, 5.2vmin, 50px); font-size: clamp(26px, 3.3vmin, 36px); line-height: 1;
}
.previous-control:hover { transform: translateY(-51%); }
.previous-control:active { transform: translateY(-49%) scale(.97); }
.header-actions {
  position: absolute; z-index: 6; right: clamp(6px, .8vw, 12px); top: 50%; transform: translateY(-50%);
  display: flex; align-items: center;
}
.header-actions .header-control { position: relative; width: clamp(42px, 5.2vmin, 50px); height: clamp(42px, 5.2vmin, 50px); }
.next-control { font-size: clamp(26px, 3.3vmin, 36px); line-height: 1; }
.live-dot {
  position: absolute; z-index: 4; left: calc(var(--header-left-space) + 8px); bottom: clamp(4px, .55vh, 7px);
  display: inline-flex; align-items: center; gap: 5px; color: var(--cyan); font-size: clamp(8px, 1.0vh, 10px);
  font-weight: 950; letter-spacing: .11em; text-transform: uppercase; pointer-events: none;
}
.live-dot::before { content: ""; width: 7px; height: 7px; border-radius: 50%; background: currentColor; box-shadow: 0 0 0 4px rgba(23,143,156,.14); animation: pulse 2s infinite; }
.live-dot[hidden] { display: none; }
@keyframes pulse { 50% { opacity: .52; box-shadow: 0 0 0 9px rgba(23,143,156,0); } }

.metrics {
  min-width: 0; min-height: 0; display: grid; grid-template-rows: repeat(10, minmax(0, 1fr)); gap: var(--gap);
  transition: opacity .16s ease, transform .16s ease, filter .16s ease;
}
.data-rows { display: contents; }
.metrics.is-busy { filter: saturate(.87) brightness(.98); }
.metric-row {
  --row-accent: #178f9c; --row-label-bg: #d4f0ee; --row-current-bg: #e6f7f3;
  min-width: 0; min-height: 0; display: grid; grid-template-columns: var(--label-width) minmax(0, 1fr);
  align-items: stretch; gap: 0; border: 0; border-radius: var(--radius); background: var(--rail-bg);
  overflow: hidden; box-shadow: 0 4px 15px rgba(40, 58, 66, .065);
}
html[data-theme="dark"] .metric-row { box-shadow: 0 4px 15px rgba(0, 0, 0, .13); }
.metric-row[data-section="sunrise_sunset"] { --row-accent:#0b9481; --row-label-bg:#c9eee3; --row-current-bg:#e1f6ef; }
.metric-row[data-section="tithi"] { --row-accent:#d99500; --row-label-bg:#ffecad; --row-current-bg:#fff7dc; }
.metric-row[data-section="nakshatra"] { --row-accent:#dd527c; --row-label-bg:#f8d2df; --row-current-bg:#fff0f5; }
.metric-row[data-section="yoga"] { --row-accent:#ee6955; --row-label-bg:#ffd8cf; --row-current-bg:#fff0ec; }
.metric-row[data-section="karana"] { --row-accent:#1695a4; --row-label-bg:#ccecf0; --row-current-bg:#e7f6f8; }
.metric-row[data-section="choghadiya"] { --row-accent:#e68516; --row-label-bg:#ffe3bd; --row-current-bg:#fff1dd; }
.metric-row[data-section="hora"] { --row-accent:#ef7259; --row-label-bg:#ffd8cf; --row-current-bg:#fff0ec; }
.metric-row[data-section="period"] { --row-accent:#6862df; --row-label-bg:#dcdbfb; --row-current-bg:#efefff; }
.metric-row[data-section="lagna"] { --row-accent:#4777cf; --row-label-bg:#d8e5f8; --row-current-bg:#ecf2fc; }
.metric-row[data-section="reserved"] { --row-accent:#bd4c82; --row-label-bg:#f2deea; --row-current-bg:#f8edf4; }

html[data-theme="dark"] .metric-row[data-section="sunrise_sunset"] { --row-label-bg:#145447; --row-current-bg:#164c43; }
html[data-theme="dark"] .metric-row[data-section="tithi"] { --row-label-bg:#57451d; --row-current-bg:#4f421f; }
html[data-theme="dark"] .metric-row[data-section="nakshatra"] { --row-label-bg:#573443; --row-current-bg:#4d3040; }
html[data-theme="dark"] .metric-row[data-section="yoga"] { --row-label-bg:#5a3932; --row-current-bg:#4c332f; }
html[data-theme="dark"] .metric-row[data-section="karana"] { --row-label-bg:#164b54; --row-current-bg:#16434c; }
html[data-theme="dark"] .metric-row[data-section="choghadiya"] { --row-label-bg:#5c3d22; --row-current-bg:#4d3522; }
html[data-theme="dark"] .metric-row[data-section="hora"] { --row-label-bg:#5a3832; --row-current-bg:#4d332f; }
html[data-theme="dark"] .metric-row[data-section="period"] { --row-label-bg:#3c3a64; --row-current-bg:#39375c; }
html[data-theme="dark"] .metric-row[data-section="lagna"] { --row-label-bg:#29466e; --row-current-bg:#29415f; }
html[data-theme="dark"] .metric-row[data-section="reserved"] { --row-label-bg:#4b3040; --row-current-bg:#3f2a38; }

.metric-label {
  min-width: 0; display: flex; align-items: center; gap: clamp(7px, .9vw, 13px); padding: 0 clamp(8px, 1.25vw, 18px);
  background: var(--row-label-bg); border-right: 1px solid rgba(30, 52, 63, .10); position: relative;
}
html[data-theme="dark"] .metric-label { border-right-color: rgba(229,240,246,.12); }
.metric-icon {
  flex: 0 0 auto; width: clamp(25px, 3.55vh, 36px); aspect-ratio: 1; display: grid; place-items: center;
  border-radius: 50%; color: var(--row-accent); background: rgba(255,255,255,.67); border: 1px solid rgba(255,255,255,.76);
  font-size: clamp(13px, 2.1vh, 20px); line-height: 1; box-shadow: 0 4px 12px rgba(40,55,63,.08);
}
html[data-theme="dark"] .metric-icon { background: rgba(255,255,255,.07); border-color: rgba(255,255,255,.13); box-shadow: none; }
.metric-label h2 {
  min-width: 0; margin: 0; color: var(--text); font-size: clamp(13px, 2.05vh, 20px); line-height: 1.16;
  padding-block: .07em; font-weight: 880; letter-spacing: -.025em; overflow-wrap: normal; word-break: normal; hyphens: none; text-wrap: balance;
}
.blank-label { padding: 0; }
.timeline-wrap { min-width: 0; min-height: 0; position: relative; overflow: hidden; background: var(--rail-bg); }
.timeline-wrap::after {
  content: ""; position: absolute; z-index: 3; right: 0; top: 0; bottom: 0; width: clamp(8px, 1.8vw, 24px);
  pointer-events: none; background: linear-gradient(270deg, var(--rail-bg), transparent);
}
.timeline {
  width: 100%; height: 100%; min-width: 0; display: flex; align-items: stretch; gap: var(--gap);
  overflow-x: auto; overflow-y: hidden; padding: clamp(3px, .42vh, 5px) clamp(15px, 2vw, 28px) clamp(3px, .42vh, 5px) 0;
  scroll-padding-inline-start: 0; scroll-snap-type: x mandatory; scrollbar-width: none; overscroll-behavior-x: contain;
  touch-action: pan-x; -webkit-overflow-scrolling: touch; cursor: grab;
}
.timeline:active { cursor: grabbing; }
.moment {
  --quality-color: transparent; --quality-bg: var(--neutral-bg); --focus-border: var(--row-accent);
  flex: 0 0 clamp(286px, 29.5vw, 420px); min-width: 0; height: 100%; scroll-snap-align: start;
  display: grid; grid-template-columns: minmax(0, 1fr) auto; grid-template-rows: auto minmax(0, 1fr); align-content: center;
  column-gap: clamp(6px, .8vw, 12px); row-gap: 1px; padding: clamp(3px, .42vh, 6px) clamp(10px, 1.15vw, 16px);
  border-radius: calc(var(--radius) - 3px); border: 2px solid transparent; background: var(--quality-bg); color: var(--text);
  transition: transform .16s ease, border-color .16s ease, background .16s ease, box-shadow .16s ease;
  position: relative; contain: layout paint; font-variant-numeric: tabular-nums;
}
.moment::before { content: ""; position: absolute; left: 0; top: 12%; bottom: 12%; width: 4px; border-radius: 0 999px 999px 0; background: var(--quality-color); opacity: 1; }
.moment.neutral { --quality-color: transparent; --quality-bg: var(--neutral-bg); --focus-border: var(--row-accent); }
.moment.auspicious { --quality-color: var(--good); --quality-bg: var(--good-bg); --focus-border: var(--good); }
.moment.inauspicious { --quality-color: var(--bad); --quality-bg: var(--bad-bg); --focus-border: var(--bad); }
.moment:hover { filter: brightness(.995); }
html[data-theme="dark"] .moment:hover { filter: brightness(1.06); }
.moment.is-current {
  border-color: var(--focus-border); background: var(--quality-bg);
  box-shadow: 0 0 0 1px rgba(255,255,255,.55) inset, 0 5px 13px rgba(28,48,58,.10);
}
.moment.is-current.neutral { background: var(--row-current-bg); }
html[data-theme="dark"] .moment.is-current { box-shadow: 0 0 0 1px rgba(255,255,255,.08) inset, 0 5px 16px rgba(0,0,0,.18); }
.moment.is-current.neutral::before { background: var(--row-accent); }
.moment-title {
  grid-column: 1; grid-row: 1; align-self: end; min-width: 0; padding-block: .07em .02em;
  white-space: nowrap; overflow: hidden; text-overflow: ellipsis; font-size: clamp(14px, 2.05vh, 19px);
  line-height: 1.16; font-weight: 900; letter-spacing: -.018em;
}
.moment-meta {
  grid-column: 1; grid-row: 2; align-self: start; min-width: 0; display: flex; flex-direction: column;
  gap: 0; color: var(--muted); line-height: 1.12; overflow: hidden;
}
.moment-date,
.moment-time {
  display: block; min-width: 0; white-space: nowrap; overflow: hidden; text-overflow: ellipsis;
  font-variant-numeric: tabular-nums;
}
.moment-date { font-size: clamp(10px, 1.30vh, 13px); font-weight: 780; }
.moment-time { font-size: clamp(11px, 1.52vh, 15px); font-weight: 730; }
.badges {
  grid-column: 2; grid-row: 1 / span 2; display: flex; flex-direction: column; align-items: flex-end; justify-content: center;
  gap: 3px; min-width: 0;
}
.badge {
  max-width: clamp(82px, 18vw, 126px); padding: clamp(2px, .30vh, 4px) clamp(6px, .65vw, 10px);
  border-radius: 999px; white-space: nowrap; overflow: hidden; text-overflow: ellipsis;
  font-size: clamp(7.5px, 1.08vh, 10.5px); line-height: 1; font-weight: 950; letter-spacing: .05em;
  text-transform: uppercase; border: 1px solid currentColor; background: rgba(255,255,255,.60);
}
html[data-theme="dark"] .badge { background: rgba(255,255,255,.06); }
.badge.good { color: #006c5b; }
.badge.bad { color: #b72f50; }
.badge.neutral { color: var(--lavender); }
html[data-theme="dark"] .badge.good { color: #8ff0d0; }
html[data-theme="dark"] .badge.bad { color: #ffb1bd; }

.reserved-row { box-shadow: none; }
.reserved-row .timeline-wrap::after { display: none; }
.reserved-slot { min-width: 0; min-height: 0; overflow: hidden; background: var(--rail-bg); display: grid; align-items: center; }
.reserved-slot .adsbygoogle { display: block; width: 100%; max-width: 100%; min-height: 0; overflow: hidden; }

.fab {
  position: fixed; z-index: 20; right: max(10px, calc((100vw - 1920px) / 2 + 14px)); bottom: max(10px, env(safe-area-inset-bottom));
  width: clamp(50px, 7.1vmin, 66px); aspect-ratio: 1; border: 1px solid rgba(221, 153, 24, .58); border-radius: 50%;
  display: grid; place-items: center; color: #6e4200; cursor: pointer;
  background: linear-gradient(145deg, #ffeeb3, #ffd274 54%, #ffbb82);
  box-shadow: 0 10px 26px rgba(80, 58, 21, .20), 0 0 0 5px rgba(247, 190, 71, .14);
  transition: transform .17s ease, box-shadow .17s ease, filter .17s ease;
}
html[data-theme="dark"] .fab { color: #331b08; border-color: rgba(255,229,181,.68); box-shadow: 0 14px 34px rgba(0,0,0,.40), 0 0 0 5px rgba(240,182,75,.10); }
.fab svg { width: 43%; height: 43%; fill: none; stroke: currentColor; stroke-width: 2.25; stroke-linecap: round; stroke-linejoin: round; }
.fab:hover { transform: translateY(-2px) rotate(-3deg); filter: brightness(1.02); }
.fab:active { transform: translateY(1px) scale(.97); }
.fab::after {
  content: attr(data-tooltip); position: absolute; right: calc(100% + 10px); top: 50%; transform: translateY(-50%) translateX(4px);
  opacity: 0; pointer-events: none; white-space: nowrap; padding: 8px 11px; border-radius: 10px;
  color: var(--text); background: var(--surface-strong); border: 1px solid var(--line-strong); font-size: 13px; font-weight: 750;
  box-shadow: var(--shadow); transition: opacity .15s ease, transform .15s ease;
}
.fab:hover::after, .fab:focus-visible::after { opacity: 1; transform: translateY(-50%) translateX(0); }

.settings-sheet {
  width: min(94vw, 650px); max-height: min(94dvh, 820px); margin: auto; padding: 0; border: 1px solid var(--line-strong);
  border-radius: clamp(20px, 4vw, 30px); color: var(--text); background: var(--surface-strong);
  box-shadow: 0 30px 90px rgba(20,32,39,.34); overflow: hidden;
}
html[data-theme="dark"] .settings-sheet { background: linear-gradient(155deg, #143246, #071b29); box-shadow: 0 35px 100px rgba(0,0,0,.64); }
.settings-sheet::backdrop { background: var(--dialog-backdrop); backdrop-filter: blur(8px) saturate(.85); }
.settings-form { max-height: min(94dvh, 820px); display: grid; grid-template-rows: auto minmax(0,1fr) auto; }
.sheet-head {
  display: flex; align-items: center; justify-content: space-between; gap: 16px; padding: clamp(16px, 3vw, 24px);
  border-bottom: 1px solid var(--line); background: linear-gradient(110deg, rgba(255, 246, 215, .62), rgba(218, 244, 244, .55));
}
html[data-theme="dark"] .sheet-head { background: rgba(255,255,255,.025); }
.sheet-head h2 { margin: 0; font-size: clamp(22px, 3.7vw, 30px); letter-spacing: -.03em; }
.icon-button {
  width: 44px; aspect-ratio: 1; border-radius: 50%; border: 1px solid var(--line); background: var(--surface-muted);
  color: var(--text); cursor: pointer; display: grid; place-items: center; font-size: 24px;
}
.icon-button:hover { filter: brightness(.98); }
.sheet-body { min-height: 0; overflow-y: auto; overscroll-behavior: contain; padding: clamp(15px, 3vw, 25px); display: grid; gap: 16px; }
.field, .theme-field { display: grid; gap: 8px; min-width: 0; margin: 0; padding: 0; border: 0; }
.field > label, .field-label, .theme-field legend { color: var(--text); font-size: 14px; font-weight: 900; letter-spacing: .035em; text-transform: uppercase; }
.theme-field legend { margin-bottom: 8px; }
.theme-options {
  display: grid; grid-template-columns: 1fr 1fr; gap: 4px; padding: 4px; border: 1px solid var(--line); border-radius: 16px; background: var(--surface-muted);
}
.theme-option { position: relative; min-width: 0; }
.theme-option input { position: absolute; opacity: 0; pointer-events: none; }
.theme-option label {
  min-height: 48px; display: flex; align-items: center; justify-content: center; gap: 8px; border: 1px solid transparent; border-radius: 12px;
  cursor: pointer; color: var(--muted); font-size: 16px; font-weight: 850; transition: .16s ease;
}
.theme-option input:checked + label { color: var(--text); background: var(--surface-strong); border-color: rgba(23,143,156,.38); box-shadow: 0 4px 15px rgba(31,48,58,.08); }
.theme-option input:focus-visible + label { outline: 3px solid rgba(23,143,156,.32); outline-offset: 2px; }
.theme-glyph { font-size: 20px; line-height: 1; }
.input-shell { position: relative; min-width: 0; }
.input-shell input, .field input, .field select {
  width: 100%; min-width: 0; height: 54px; border: 1px solid var(--line-strong); border-radius: 14px;
  color: var(--text); background: var(--surface-muted); padding: 0 14px; outline: none; font-size: 17px;
  transition: border-color .15s ease, box-shadow .15s ease, background .15s ease;
}
.field select { appearance: none; background-image: linear-gradient(45deg, transparent 50%, var(--muted) 50%), linear-gradient(135deg, var(--muted) 50%, transparent 50%); background-position: calc(100% - 19px) 23px, calc(100% - 13px) 23px; background-size: 6px 6px; background-repeat: no-repeat; padding-right: 40px; }
.input-shell input:focus, .field input:focus, .field select:focus { border-color: rgba(23,143,156,.70); box-shadow: 0 0 0 4px rgba(23,143,156,.12); background: var(--surface-strong); }
.field input:disabled { opacity: .64; cursor: not-allowed; }
.place-results { display: grid; gap: 6px; margin-top: 8px; max-height: 220px; overflow-y: auto; border-radius: 13px; }
.place-result {
  width: 100%; min-height: 50px; display: grid; grid-template-columns: minmax(0,1fr) auto; align-items: center; gap: 10px; text-align: left; cursor: pointer;
  color: var(--text); background: var(--surface-muted); border: 1px solid var(--line); border-radius: 12px; padding: 10px 12px;
}
.place-result:hover, .place-result:focus-visible { border-color: rgba(23,143,156,.48); background: var(--surface-strong); }
.place-main { min-width: 0; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; font-size: 15px; font-weight: 800; }
.place-sub { color: var(--muted); font-size: 12px; white-space: nowrap; }
.form-grid { display: grid; grid-template-columns: repeat(2, minmax(0,1fr)); gap: 13px; }
.switch-row { display: flex; align-items: center; justify-content: space-between; gap: 14px; min-height: 48px; padding: 0 2px; }
.switch-row > label { font-size: 16px; font-weight: 820; color: var(--text); }
.switch-locked { display: inline-flex; align-items: center; gap: 9px; }
.switch-state { color: var(--text); font-size: 12px; line-height: 1; font-weight: 950; letter-spacing: .09em; text-transform: uppercase; }
.switch { position: relative; width: 54px; height: 30px; flex: 0 0 auto; }
.switch input { position: absolute; opacity: 0; pointer-events: none; }
.switch-track { position: absolute; inset: 0; border-radius: 999px; background: #d9e0e4; border: 1px solid var(--line-strong); transition: .18s ease; cursor: default; }
html[data-theme="dark"] .switch-track { background: rgba(255,255,255,.14); }
.switch-track::after { content: ""; position: absolute; width: 22px; height: 22px; left: 3px; top: 3px; border-radius: 50%; background: #fff; box-shadow: 0 2px 8px rgba(0,0,0,.18); transition: .18s ease; }
.switch input:checked + .switch-track { background: #bde9dc; border-color: rgba(17,141,120,.50); }
html[data-theme="dark"] .switch input:checked + .switch-track { background: rgba(87,213,173,.28); border-color: rgba(87,213,173,.55); }
.switch input:checked + .switch-track::after { transform: translateX(24px); background: var(--mint); }
.switch input:focus-visible + .switch-track { box-shadow: 0 0 0 4px rgba(23,143,156,.14); }
.location-button {
  min-height: 52px; border: 1px solid rgba(23,143,156,.34); border-radius: 14px; color: #0a6c78;
  background: #d9f2f4; cursor: pointer; font-size: 17px; font-weight: 850;
}
html[data-theme="dark"] .location-button { color: #ddfbff; background: rgba(85,208,220,.10); }
.location-button:hover { filter: brightness(.98); border-color: rgba(23,143,156,.58); }
.sheet-note { margin: 0; color: var(--muted); font-size: 13px; line-height: 1.52; }
.share-preview { margin: 2px 0 0; display: grid; gap: 9px; }
.share-preview figcaption { display: grid; gap: 3px; line-height: 1.32; }
.share-preview figcaption strong { color: var(--text); font-size: 16px; font-weight: 900; }
.share-preview figcaption span { color: var(--muted); font-size: 13px; font-weight: 620; }
.share-preview-frame {
  position: relative; width: 100%; aspect-ratio: 1200 / 630; overflow: hidden; border: 1px solid var(--line-strong);
  border-radius: 16px; background: var(--surface-muted); box-shadow: 0 10px 28px rgba(40, 48, 78, .10);
}
.share-preview-frame::after {
  content: ""; position: absolute; inset: 0; pointer-events: none; border-radius: inherit;
  box-shadow: inset 0 0 0 1px rgba(255,255,255,.32);
}
.share-preview-frame img { display: block; width: 100%; height: 100%; object-fit: cover; }
.share-preview-frame img[aria-busy="true"] { opacity: .55; }
.sheet-actions {
  display: grid; grid-template-columns: 1fr 1.55fr; gap: 11px; padding: clamp(14px, 3vw, 23px);
  border-top: 1px solid var(--line); background: var(--surface-muted);
}
.action-button { min-height: 54px; border-radius: 15px; border: 1px solid var(--line-strong); cursor: pointer; font-size: 17px; font-weight: 900; }
.action-button.secondary { color: var(--text); background: var(--surface-strong); }
.action-button.primary { color: #684200; background: linear-gradient(135deg, #ffec9e, #ffd26a); border-color: rgba(218,153,18,.52); box-shadow: 0 8px 21px rgba(201,143,25,.13); }
.action-button:hover { filter: brightness(1.02); }

.toast {
  position: fixed; z-index: 50; left: 50%; bottom: max(17px, env(safe-area-inset-bottom)); transform: translate(-50%, 18px);
  max-width: min(90vw, 560px); padding: 11px 15px; border-radius: 13px; color: var(--text);
  background: var(--surface-strong); border: 1px solid var(--line-strong); box-shadow: var(--shadow);
  font-size: 14px; font-weight: 750; opacity: 0; pointer-events: none; transition: opacity .18s ease, transform .18s ease;
}
.toast.show { opacity: 1; transform: translate(-50%, 0); }
.loading-mask {
  position: fixed; z-index: 40; inset: 0; display: grid; place-items: center; pointer-events: none; opacity: 0;
  background: rgba(24,37,44,.16); transition: opacity .12s ease;
}
.loading-mask.show { opacity: 1; }
.spinner { width: 40px; aspect-ratio: 1; border-radius: 50%; border: 3px solid rgba(115,125,132,.22); border-top-color: var(--gold); animation: spin .7s linear infinite; }
@keyframes spin { to { transform: rotate(360deg); } }

/* ------------------------------------------------------------------------
   Balanced modern visual system
   ------------------------------------------------------------------------
   The interface uses one restrained indigo family, cool neutral surfaces and
   a small teal accent. Green, rose and amber remain reserved for meaningful
   auspicious, avoid and mixed states so the dense timelines stay easy to scan.
*/
:root {
  --bg: #f2f4f9;
  --bg-soft: #fbfcff;
  --surface: rgba(255, 255, 255, .96);
  --surface-strong: #ffffff;
  --surface-muted: #edf1f7;
  --rail-bg: rgba(249, 250, 253, .96);
  --line: rgba(57, 66, 90, .11);
  --line-strong: rgba(57, 66, 90, .20);
  --text: #182033;
  --muted: #677187;
  --accent: #5c64d8;
  --accent-deep: #4149b8;
  --accent-soft: #eef0ff;
  --teal: #178b9c;
  --teal-soft: #eaf7f8;
  --gold: #bd7e18;
  --gold-soft: #fff4da;
  --cyan: #178b9c;
  --mint: #1b9874;
  --rose: #d05269;
  --lavender: #5c64d8;
  --peach: #cf765b;
  --good: #178a68;
  --good-bg: #edf8f4;
  --bad: #ca4d65;
  --bad-bg: #fff0f3;
  --mixed: #ad741d;
  --mixed-bg: #fff7e8;
  --neutral-bg: #f3f5fa;
  --current-border: #7079e2;
  --shadow: 0 13px 34px rgba(40, 48, 78, .10);
  --dialog-backdrop: rgba(22, 28, 48, .46);
}

html[data-theme="dark"] {
  --bg: #0e1421;
  --bg-soft: #151c2b;
  --surface: rgba(24, 31, 47, .97);
  --surface-strong: #1b2334;
  --surface-muted: #222c3f;
  --rail-bg: rgba(20, 27, 42, .97);
  --line: rgba(229, 234, 255, .10);
  --line-strong: rgba(229, 234, 255, .19);
  --text: #f4f6fc;
  --muted: #aab4c7;
  --accent: #9ca5ff;
  --accent-deep: #c0c5ff;
  --accent-soft: #293053;
  --teal: #62c7d0;
  --teal-soft: #19333b;
  --gold: #e7ba65;
  --gold-soft: #3a3020;
  --cyan: #62c7d0;
  --mint: #61d0aa;
  --rose: #ff8ca0;
  --lavender: #aab1ff;
  --peach: #f2a18b;
  --good: #61d0aa;
  --good-bg: #18342f;
  --bad: #ff879b;
  --bad-bg: #3a2530;
  --mixed: #e7bd69;
  --mixed-bg: #3a3122;
  --neutral-bg: #20293a;
  --current-border: #9ca5ff;
  --shadow: 0 16px 42px rgba(0, 0, 0, .34);
  --dialog-backdrop: rgba(4, 7, 15, .74);
}

body {
  background:
    radial-gradient(55vmax 38vmax at 103% -12%, rgba(92, 100, 216, .13), transparent 62%),
    radial-gradient(46vmax 34vmax at -10% 108%, rgba(23, 139, 156, .09), transparent 64%),
    linear-gradient(145deg, var(--bg-soft), var(--bg));
}
html[data-theme="dark"] body {
  background:
    radial-gradient(58vmax 40vmax at 105% -15%, rgba(125, 136, 255, .13), transparent 62%),
    radial-gradient(46vmax 34vmax at -10% 108%, rgba(68, 173, 186, .09), transparent 64%),
    linear-gradient(145deg, var(--bg-soft), var(--bg));
}
.ambient::before {
  border-color: rgba(92, 100, 216, .14);
  box-shadow: 0 0 70px rgba(92, 100, 216, .035) inset;
  opacity: .64;
}
.ambient::after {
  border-color: rgba(23, 139, 156, .13);
  box-shadow: 0 0 70px rgba(23, 139, 156, .03) inset;
  opacity: .58;
}

.day-carousel,
html[data-theme="dark"] .day-carousel {
  color: var(--text);
  border-color: color-mix(in srgb, var(--accent) 25%, var(--line));
  background: linear-gradient(112deg, var(--surface-strong) 0%, var(--accent-soft) 58%, var(--teal-soft) 100%);
  box-shadow: var(--shadow), inset 0 1px 0 rgba(255,255,255,.55);
}
.day-carousel::before {
  background:
    radial-gradient(38% 150% at 0 50%, rgba(92, 100, 216, .08), transparent 72%),
    radial-gradient(32% 150% at 100% 50%, rgba(23, 139, 156, .08), transparent 72%);
}
.header-control,
html[data-theme="dark"] .header-control {
  color: var(--accent-deep);
  border-color: color-mix(in srgb, var(--accent) 24%, var(--line));
  background: color-mix(in srgb, var(--surface-strong) 92%, var(--accent-soft));
  box-shadow: 0 6px 16px rgba(46, 54, 91, .10), inset 0 1px 0 rgba(255,255,255,.55);
}
.header-control:hover,
html[data-theme="dark"] .header-control:hover {
  color: var(--accent-deep);
  border-color: color-mix(in srgb, var(--accent) 55%, var(--line));
  background: var(--accent-soft);
}
.live-dot { color: var(--teal); }
.live-dot::before { box-shadow: 0 0 0 4px color-mix(in srgb, var(--teal) 16%, transparent); }

.metric-row,
html[data-theme="dark"] .metric-row,
.metric-row[data-section] {
  --row-accent: var(--accent);
  --row-label-bg: var(--surface-muted);
  --row-current-bg: var(--surface-strong);
  background: var(--rail-bg);
  box-shadow: 0 4px 15px rgba(36, 44, 73, .065);
}
html[data-theme="dark"] .metric-row,
html[data-theme="dark"] .metric-row[data-section] {
  --row-accent: var(--accent);
  --row-label-bg: var(--surface-muted);
  --row-current-bg: var(--surface-strong);
  box-shadow: 0 4px 15px rgba(0, 0, 0, .18);
}
.metric-row[data-section="sunrise_sunset"] { --row-accent: var(--gold); }
.metric-row[data-section="reserved"] { --row-accent: var(--accent); }
.metric-label,
html[data-theme="dark"] .metric-label {
  color: var(--text);
  background: linear-gradient(135deg, var(--row-label-bg), color-mix(in srgb, var(--row-label-bg) 72%, var(--accent-soft)));
  border-right-color: var(--line);
}
.metric-icon,
html[data-theme="dark"] .metric-icon {
  color: var(--row-accent);
  background: color-mix(in srgb, var(--surface-strong) 78%, var(--accent-soft));
  border-color: color-mix(in srgb, var(--row-accent) 18%, var(--line));
  box-shadow: 0 4px 12px rgba(50, 58, 93, .07);
}
.timeline-wrap { background: var(--rail-bg); }

.moment,
.moment.neutral,
.moment.auspicious,
.moment.inauspicious {
  --quality-bg: var(--neutral-bg);
  --quality-color: transparent;
  --focus-border: var(--current-border);
  color: var(--text);
  background: var(--neutral-bg);
  border-color: transparent;
  box-shadow: none;
}
.moment::before { display: none; }
.moment.auspicious {
  --quality-bg: var(--good-bg);
  --focus-border: var(--good);
  background: var(--good-bg);
  border-color: color-mix(in srgb, var(--good) 52%, transparent);
}
.moment.inauspicious {
  --quality-bg: var(--bad-bg);
  --focus-border: var(--bad);
  background: var(--bad-bg);
  border-color: color-mix(in srgb, var(--bad) 52%, transparent);
}
.moment.mixed {
  --quality-bg: var(--mixed-bg);
  --focus-border: var(--mixed);
  background: var(--mixed-bg);
  border-color: color-mix(in srgb, var(--mixed) 50%, transparent);
}
.moment.is-current,
.moment.is-current.neutral,
html[data-theme="dark"] .moment.is-current,
html[data-theme="dark"] .moment.is-current.neutral {
  color: var(--text);
  border-color: var(--focus-border);
  background: var(--quality-bg);
  box-shadow: 0 0 0 1px rgba(255,255,255,.32) inset, 0 5px 15px rgba(49, 57, 96, .11);
}
.moment.is-current.neutral,
html[data-theme="dark"] .moment.is-current.neutral { background: var(--surface-strong); }
html[data-theme="dark"] .moment.is-current { box-shadow: 0 0 0 1px rgba(255,255,255,.06) inset, 0 6px 16px rgba(0,0,0,.27); }
.moment-title { color: var(--text); }
.moment-time { grid-column: 1 / -1; color: var(--muted); }
.badges { grid-row: 1; align-self: end; }
.badge,
html[data-theme="dark"] .badge {
  border-color: var(--line-strong);
  background: var(--surface-strong);
}
.badge.good,
html[data-theme="dark"] .badge.good {
  color: var(--good);
  border-color: color-mix(in srgb, var(--good) 58%, var(--line));
  background: var(--good-bg);
}
.badge.bad,
html[data-theme="dark"] .badge.bad {
  color: var(--bad);
  border-color: color-mix(in srgb, var(--bad) 58%, var(--line));
  background: var(--bad-bg);
}
.badge.neutral,
html[data-theme="dark"] .badge.neutral {
  color: var(--mixed);
  border-color: color-mix(in srgb, var(--mixed) 56%, var(--line));
  background: var(--mixed-bg);
}

.reserved-row,
html[data-theme="dark"] .reserved-row {
  background: transparent;
  box-shadow: none;
}
.reserved-row .metric-label,
.reserved-slot { background: transparent; }

.fab,
html[data-theme="dark"] .fab {
  color: #ffffff;
  border-color: color-mix(in srgb, var(--accent) 76%, var(--accent-deep));
  background: linear-gradient(145deg, #7078e8, #515acb 60%, #424ab7);
  box-shadow: 0 12px 28px rgba(67, 75, 180, .28), 0 0 0 5px rgba(92,100,216,.11);
}
html[data-theme="dark"] .fab {
  color: #111728;
  border-color: #aeb5ff;
  background: linear-gradient(145deg, #c2c6ff, #949eff 62%, #77bcc8);
  box-shadow: 0 14px 34px rgba(0,0,0,.44), 0 0 0 5px rgba(156,165,255,.10);
}

.settings-sheet,
html[data-theme="dark"] .settings-sheet {
  background: var(--surface-strong);
  border-color: color-mix(in srgb, var(--accent) 18%, var(--line-strong));
}
.sheet-head,
html[data-theme="dark"] .sheet-head {
  color: var(--text);
  background: linear-gradient(112deg, var(--accent-soft), color-mix(in srgb, var(--teal-soft) 65%, var(--surface-muted)));
}
.theme-option input:checked + label {
  color: var(--accent-deep);
  border-color: color-mix(in srgb, var(--accent) 62%, var(--line));
  background: var(--accent-soft);
  box-shadow: 0 5px 16px rgba(67, 75, 180, .10);
}
.theme-option input:focus-visible + label { outline-color: var(--accent); }
.place-result:hover,
.place-result:focus-visible { border-color: var(--accent); background: var(--accent-soft); }
.switch input:focus-visible + .switch-track { box-shadow: 0 0 0 4px color-mix(in srgb, var(--accent) 17%, transparent); }
.input-shell input:focus,
.field input:focus,
.field select:focus {
  border-color: var(--accent);
  box-shadow: 0 0 0 4px color-mix(in srgb, var(--accent) 14%, transparent);
}
.switch input:checked + .switch-track,
html[data-theme="dark"] .switch input:checked + .switch-track {
  border-color: var(--accent);
  background: var(--accent);
}
.switch input:checked + .switch-track::after {
  background: #ffffff;
  border: 1px solid color-mix(in srgb, var(--accent) 25%, var(--line));
}
.location-button,
html[data-theme="dark"] .location-button {
  color: var(--accent-deep);
  border-color: color-mix(in srgb, var(--accent) 28%, var(--line));
  background: var(--accent-soft);
}
.location-button:hover { border-color: var(--accent); }
.action-button.primary,
html[data-theme="dark"] .action-button.primary {
  color: #ffffff;
  border-color: var(--accent-deep);
  background: linear-gradient(135deg, var(--accent), var(--accent-deep));
  box-shadow: 0 8px 20px rgba(67, 75, 180, .18);
}
.spinner { border-top-color: var(--accent); }
:focus-visible { outline-color: var(--accent); }

:focus-visible { outline: 3px solid var(--accent); outline-offset: 3px; }

@media (min-width: 900px) {
  :root { --label-width: clamp(240px, 20vw, 300px); }
  .moment { flex-basis: clamp(340px, 29.5vw, 425px); }
}

@media (max-width: 560px) {
  :root {
    --label-width: clamp(108px, 31vw, 126px);
    --header-left-space: 48px;
    --header-right-space: 48px;
    --header-height: clamp(58px, 7.8vh, 68px);
  }
  .header-full { display: none; }
  .header-compact { display: inline; }
  .day-panel { padding-left: calc(var(--header-left-space) + 3px); padding-right: calc(var(--header-right-space) + 3px); }
  .day-title { font-size: clamp(15px, 4.45vw, 20px); letter-spacing: -.035em; }
  .previous-control { left: 5px; width: 42px; height: 42px; min-width: 42px; min-height: 42px; }
  .header-actions { right: 5px; }
  .header-actions .header-control { width: 42px; height: 42px; min-width: 42px; min-height: 42px; }
  .live-dot { display: none; }
  .metric-label { gap: 6px; padding-inline: 7px; }
  .metric-icon { width: clamp(22px, 3.25vh, 29px); font-size: clamp(12px, 1.9vh, 16px); }
  .metric-label h2 { font-size: clamp(13px, 1.90vh, 16px); line-height: 1.12; }
  .timeline { padding-left: 0; padding-right: 20px; }
  .moment { flex-basis: calc(100vw - var(--label-width) - (2 * var(--pad)) - 3px); min-width: 0; max-width: 360px; padding-inline: 8px; column-gap: 5px; }
  .moment-title { font-size: clamp(14px, 1.95vh, 16.5px); }
  .moment-date { font-size: clamp(9.5px, 1.22vh, 11.5px); }
  .moment-time { font-size: clamp(10.5px, 1.42vh, 13.5px); }
  .badge { max-width: 82px; padding-inline: 5px; }
  .fab { width: 52px; right: 9px; bottom: max(9px, env(safe-area-inset-bottom)); }
  .fab::after { display: none; }
  .form-grid { grid-template-columns: 1fr; }
}

@media (max-width: 360px) {
  :root { --label-width: 108px; --header-left-space: 45px; --header-right-space: 45px; }
  .day-title { font-size: clamp(13px, 4.2vw, 15.5px); }
  .previous-control, .header-actions .header-control { width: 38px; height: 38px; min-width: 38px; min-height: 38px; }
  .metric-label { padding-inline: 5px; gap: 5px; }
  .metric-icon { width: 20px; }
  .metric-label h2 { font-size: 12.8px; line-height: 1.10; }
  .moment { padding-inline: 7px; }
  .moment-title { font-size: 13.4px; }
  .moment-date { font-size: 9px; }
  .moment-time { font-size: 10.4px; }
  .badge { font-size: 7px; padding: 2px 4px; max-width: 72px; }
  .fab { width: 47px; }
}

@media (max-height: 640px) {
  :root { --gap: 2px; --pad: 4px; --radius: 10px; --header-height: 46px; }
  .day-title { font-size: clamp(13px, 2.55vw, 25px); }
  .previous-control, .header-actions .header-control { width: 38px; height: 38px; min-width: 38px; min-height: 38px; }
  .live-dot { display: none; }
  .metric-label { padding-inline: 6px; gap: 5px; }
  .metric-icon { width: 19px; font-size: 10px; }
  .metric-label h2 { font-size: clamp(12px, 2.25vh, 13px); line-height: 1.10; }
  .timeline { padding-block: 2px; }
  .moment { padding-inline: 7px; column-gap: 5px; }
  .moment-title { font-size: clamp(12.5px, 2.25vh, 14px); }
  .moment-date { font-size: clamp(8.5px, 1.45vh, 10px); }
  .moment-time { font-size: clamp(9.5px, 1.75vh, 11.5px); }
  .badge { font-size: clamp(7px, 1.45vh, 8px); padding: 2px 4px; max-width: 72px; }
  .fab { width: 44px; }
}

@media (orientation: landscape) and (max-height: 480px) {
  :root { --label-width: clamp(122px, 19vw, 198px); --header-height: 40px; }
  .day-title { font-size: clamp(12px, 2.1vw, 20px); }
  .previous-control, .header-actions .header-control { width: 30px; height: 30px; min-width: 30px; min-height: 30px; font-size: 23px; }
  .moment { flex-basis: clamp(300px, 43vw, 455px); grid-template-rows: 1fr; grid-template-columns: minmax(0,.9fr) minmax(0,1.35fr) auto; padding: 1px 7px; column-gap: 6px; }
  .metric-label h2 { font-size: 10.5px; }
  .moment-title { grid-column: 1; grid-row: 1; align-self: center; padding: .05em 0; font-size: 10.5px; line-height: 1.12; }
  .moment-meta { grid-column: 2; grid-row: 1; align-self: center; display: flex; flex-direction: column; min-width: 0; text-align: right; line-height: 1.03; }
  .moment-date { font-size: 7.5px; }
  .moment-time { font-size: 8.5px; }
  .badges { grid-column: 3; grid-row: 1; margin-left: 2px; gap: 1px; }
  .badge { font-size: 6.5px; padding: 1px 4px; }
  .fab { width: 36px; right: 6px; bottom: 6px; }
}

html:lang(hi) .day-title, html:lang(mr) .day-title, html:lang(ne) .day-title, html:lang(sa) .day-title,
html:lang(gu) .day-title, html:lang(bn) .day-title, html:lang(ta) .day-title, html:lang(te) .day-title,
html:lang(kn) .day-title, html:lang(ml) .day-title, html:lang(pa) .day-title, html:lang(or) .day-title,
html:lang(hi) .metric-label h2, html:lang(mr) .metric-label h2, html:lang(ne) .metric-label h2, html:lang(sa) .metric-label h2,
html:lang(gu) .metric-label h2, html:lang(bn) .metric-label h2, html:lang(ta) .metric-label h2, html:lang(te) .metric-label h2,
html:lang(kn) .metric-label h2, html:lang(ml) .metric-label h2, html:lang(pa) .metric-label h2, html:lang(or) .metric-label h2,
html:lang(hi) .moment-title, html:lang(mr) .moment-title, html:lang(ne) .moment-title, html:lang(sa) .moment-title,
html:lang(gu) .moment-title, html:lang(bn) .moment-title, html:lang(ta) .moment-title, html:lang(te) .moment-title,
html:lang(kn) .moment-title, html:lang(ml) .moment-title, html:lang(pa) .moment-title, html:lang(or) .moment-title {
  line-height: 1.24; padding-top: .12em; padding-bottom: .04em;
}

/* ------------------------------------------------------------------------
   Refined interaction and typography pass
   ------------------------------------------------------------------------ */
:root {
  --moment-min: 132px;
  --moment-max: 980px;
}
body {
  font-family: Inter, ui-sans-serif, system-ui, -apple-system, BlinkMacSystemFont, "Segoe UI",
    "Noto Sans", "Noto Sans Devanagari", "Noto Sans Gujarati", "Noto Sans Bengali",
    "Noto Sans Tamil", "Noto Sans Telugu", "Noto Sans Kannada", "Noto Sans Malayalam",
    "Noto Sans Gurmukhi", "Noto Sans Oriya", "Noto Sans Odia", "Nirmala UI", sans-serif;
  font-weight: 400;
  letter-spacing: -.006em;
}
.day-title { font-weight: 680; letter-spacing: -.032em; }
.metric-label h2 { font-weight: 620; letter-spacing: -.014em; }
.moment {
  flex: 0 0 clamp(var(--moment-min), var(--duration-width, 280px), var(--moment-max));
  border-width: 1px;
}
.moment.starts-day:not(:first-child) { margin-inline-start: clamp(6px, .65vw, 12px); }
.moment.starts-day:not(:first-child)::after {
  content: "";
  position: absolute;
  inset-block: 10%;
  inset-inline-start: calc(-1 * clamp(4px, .40vw, 7px));
  width: 1px;
  background: var(--line-strong);
}
.moment-title {
  font-weight: 650;
  letter-spacing: -.012em;
}
.moment-date { font-weight: 480; }
.moment-time { font-weight: 560; }
.badge { font-weight: 700; letter-spacing: .035em; }
.live-dot { font-weight: 700; }
.fab::after { font-weight: 560; }

.settings-sheet {
  width: min(92vw, 520px);
  max-height: min(92dvh, 740px);
  border-radius: 20px;
}
.settings-form { max-height: min(92dvh, 740px); }
.sheet-head { gap: 10px; padding: 11px 14px 11px 16px; }
.sheet-head h2 { font-size: clamp(17px, 3.4vw, 20px); font-weight: 650; letter-spacing: -.018em; }
.icon-button { width: 34px; font-size: 20px; }
.sheet-body { padding: 12px 16px 14px; gap: 10px; }
.field { gap: 5px; }
.field > label, .field-label {
  font-size: 12px;
  font-weight: 620;
  letter-spacing: .018em;
  text-transform: none;
}
.theme-toggle-button {
  justify-self: start;
  min-height: 34px;
  display: inline-flex;
  align-items: center;
  gap: 7px;
  padding: 0 11px;
  border: 1px solid var(--line-strong);
  border-radius: 999px;
  color: var(--accent-deep);
  background: var(--accent-soft);
  cursor: pointer;
  font-size: 13px;
  font-weight: 620;
}
.theme-toggle-button:hover { border-color: var(--accent); }
.theme-toggle-button .theme-glyph { font-size: 15px; }
.input-shell input, .field input, .field select {
  height: 42px;
  border-radius: 10px;
  padding-inline: 11px;
  font-size: 14px;
  font-weight: 440;
}
.field select {
  background-position: calc(100% - 17px) 18px, calc(100% - 12px) 18px;
  background-size: 5px 5px;
  padding-right: 34px;
}
.place-results { gap: 4px; margin-top: 4px; max-height: 164px; border-radius: 10px; }
.place-result { min-height: 42px; gap: 8px; border-radius: 9px; padding: 7px 10px; }
.place-main { font-size: 13px; font-weight: 580; }
.place-sub { font-size: 11px; }
.form-grid { gap: 9px; }
.switch-row { min-height: 38px; padding: 1px 0; }
.switch-row > label { font-size: 13px; font-weight: 580; }
.switch { width: 44px; height: 24px; }
.switch input { pointer-events: auto; cursor: pointer; }
.switch-track { cursor: pointer; }
.switch-track::after { width: 18px; height: 18px; left: 2px; top: 2px; }
.switch input:checked + .switch-track::after { transform: translateX(20px); }
.location-button { min-height: 42px; border-radius: 10px; font-size: 14px; font-weight: 620; }
.share-preview { margin: 0; gap: 0; }
.share-preview-frame { border-radius: 11px; box-shadow: 0 7px 20px rgba(40,48,78,.08); }
.sheet-actions { gap: 8px; padding: 10px 16px 12px; }
.action-button { min-height: 42px; border-radius: 10px; font-size: 14px; font-weight: 650; }

@media (max-width: 560px) {
  :root { --moment-min: 154px; --moment-max: 690px; }
  .moment { flex-basis: clamp(var(--moment-min), var(--duration-width-mobile, 250px), var(--moment-max)); }
  .settings-sheet { width: min(94vw, 500px); max-height: 94dvh; }
  .settings-form { max-height: 94dvh; }
  .sheet-body { padding-inline: 13px; }
  .sheet-actions { padding-inline: 13px; }
}

@media (orientation: landscape) and (max-height: 480px) {
  :root { --moment-min: 148px; --moment-max: 760px; }
  .moment { flex-basis: clamp(var(--moment-min), var(--duration-width-landscape, 250px), var(--moment-max)); }
  .settings-sheet { width: min(86vw, 620px); max-height: 96dvh; }
  .settings-form { max-height: 96dvh; }
  .sheet-head { padding-block: 7px; }
  .sheet-body { padding-block: 8px; gap: 7px; }
  .input-shell input, .field input, .field select { height: 36px; }
  .location-button, .action-button { min-height: 36px; }
  .share-preview-frame { max-width: 330px; justify-self: center; }
}

/* ------------------------------------------------------------------------
   Pro readability pass: modern weights, true duration cues, compact editor
   ------------------------------------------------------------------------ */
:root {
  --moment-min: 176px;
  --moment-max: 1080px;
}
body {
  font-family: "Segoe UI Variable Text", "Aptos", Inter, ui-sans-serif, system-ui,
    -apple-system, BlinkMacSystemFont, "Segoe UI", "Noto Sans",
    "Noto Sans Devanagari", "Noto Sans Gujarati", "Noto Sans Bengali",
    "Noto Sans Tamil", "Noto Sans Telugu", "Noto Sans Kannada",
    "Noto Sans Malayalam", "Noto Sans Gurmukhi", "Noto Sans Oriya",
    "Noto Sans Odia", "Nirmala UI", sans-serif;
  font-weight: 400;
  letter-spacing: -.004em;
  text-rendering: optimizeLegibility;
}
.day-title {
  font-weight: 610;
  letter-spacing: -.027em;
}
.metric-label h2 {
  font-weight: 560;
  letter-spacing: -.009em;
}
.moment {
  grid-template-columns: minmax(0, 1fr);
  column-gap: 0;
  max-width: none;
}
.moment-title {
  grid-column: 1;
  font-weight: 590;
  letter-spacing: -.008em;
}
.moment-meta { grid-column: 1; }
.moment-date { font-weight: 420; }
.moment-time { font-weight: 510; }
.moment-endpoint { overflow: visible; text-overflow: clip; white-space: nowrap; }
.moment-endpoint-end { color: var(--muted); }
.badges { display: none !important; }
.live-dot { font-weight: 650; }
.fab::after { font-weight: 520; }

.settings-sheet {
  width: min(91vw, 455px);
  max-height: min(94dvh, 690px);
  border-radius: 17px;
}
.settings-form { max-height: min(94dvh, 690px); }
.sheet-head {
  gap: 8px;
  padding: 9px 11px 9px 14px;
}
.sheet-head h2 {
  font-size: clamp(16px, 3vw, 18px);
  font-weight: 590;
  letter-spacing: -.012em;
}
.icon-button { width: 32px; font-size: 19px; }
.sheet-body {
  padding: 9px 13px 10px;
  gap: 7px;
}
.field { gap: 4px; }
.field > label, .field-label {
  font-size: 11.5px;
  line-height: 1.28;
  font-weight: 560;
  letter-spacing: .006em;
}
.theme-toggle-button {
  min-height: 30px;
  gap: 6px;
  padding: 0 9px;
  font-size: 12px;
  font-weight: 560;
}
.theme-toggle-button .theme-glyph { font-size: 13px; }
.input-shell input, .field input, .field select {
  height: 38px;
  border-radius: 9px;
  padding-inline: 10px;
  font-size: 13.5px;
  font-weight: 400;
}
.field select {
  background-position: calc(100% - 16px) 16px, calc(100% - 11px) 16px;
  padding-right: 32px;
}
.form-grid { gap: 7px; }
.switch-row {
  min-height: 34px;
  gap: 10px;
  padding: 0;
}
.switch-row > label {
  font-size: 12.5px;
  line-height: 1.3;
  font-weight: 540;
}
.switch { width: 40px; height: 22px; }
.switch-track::after { width: 16px; height: 16px; left: 2px; top: 2px; }
.switch input:checked + .switch-track::after { transform: translateX(18px); }
.location-button {
  min-height: 38px;
  border-radius: 9px;
  font-size: 13.5px;
  font-weight: 560;
}
.share-preview-frame {
  width: min(100%, 292px);
  justify-self: center;
  border-radius: 9px;
  box-shadow: 0 5px 16px rgba(40,48,78,.07);
}
.sheet-actions {
  gap: 7px;
  padding: 8px 13px 10px;
}
.action-button {
  min-height: 38px;
  border-radius: 9px;
  font-size: 13.5px;
  font-weight: 580;
}

@media (max-width: 560px) {
  :root { --moment-min: 182px; --moment-max: 760px; }
  .moment {
    flex-basis: clamp(var(--moment-min), var(--duration-width-mobile, 250px), var(--moment-max));
    max-width: none;
  }
  .settings-sheet { width: min(92vw, 455px); max-height: 94dvh; }
  .settings-form { max-height: 94dvh; }
  .sheet-body { padding-inline: 12px; }
  .sheet-actions { padding-inline: 12px; }
}

@media (orientation: landscape) and (max-height: 480px) {
  :root { --moment-min: 160px; --moment-max: 900px; }
  .moment {
    flex-basis: clamp(var(--moment-min), var(--duration-width-landscape, 250px), var(--moment-max));
    max-width: none;
  }
  .settings-sheet { width: min(82vw, 520px); max-height: 96dvh; }
  .settings-form { max-height: 96dvh; }
  .sheet-head { padding-block: 6px; }
  .sheet-body { padding-block: 6px; gap: 5px; }
  .input-shell input, .field input, .field select { height: 32px; }
  .date-picker-shell { height: 32px; }
  .location-button, .action-button { min-height: 32px; }
  .share-preview-frame { max-width: 230px; }
}


/* ------------------------------------------------------------------------
   Celestial masthead: one confident, modern anchor for the Panchang
   ------------------------------------------------------------------------ */
:root {
  --header-start: #29386f;
  --header-mid: #4057a5;
  --header-end: #28727a;
  --header-text: #fbfdff;
  --header-muted: rgba(247, 250, 255, .74);
  --header-control-bg: rgba(255, 255, 255, .13);
  --header-control-hover: rgba(255, 255, 255, .22);
  --header-control-line: rgba(255, 255, 255, .30);
  --header-live: #c9fff1;
}
html[data-theme="dark"] {
  --header-start: #171f43;
  --header-mid: #273b73;
  --header-end: #18545c;
  --header-text: #fbfdff;
  --header-muted: rgba(237, 243, 255, .70);
  --header-control-bg: rgba(255, 255, 255, .11);
  --header-control-hover: rgba(255, 255, 255, .18);
  --header-control-line: rgba(255, 255, 255, .24);
  --header-live: #bdf7e8;
}
.day-carousel,
html[data-theme="dark"] .day-carousel {
  color: var(--header-text);
  border-color: rgba(50, 67, 125, .30);
  background:
    radial-gradient(48% 230% at 2% 50%, rgba(248, 195, 83, .20), transparent 61%),
    radial-gradient(44% 220% at 100% 50%, rgba(137, 230, 224, .15), transparent 64%),
    linear-gradient(112deg, var(--header-start) 0%, var(--header-mid) 52%, var(--header-end) 100%);
  box-shadow: 0 12px 30px rgba(37, 48, 91, .20), inset 0 1px 0 rgba(255,255,255,.14);
}
.day-carousel::before {
  background:
    linear-gradient(90deg, rgba(255,255,255,.035), transparent 28%, transparent 72%, rgba(255,255,255,.035)),
    radial-gradient(38% 180% at 22% 50%, rgba(255,255,255,.055), transparent 72%);
}
.day-carousel::after {
  content: "";
  position: absolute;
  z-index: 2;
  inset: auto 10% 0;
  height: 1px;
  pointer-events: none;
  background: linear-gradient(90deg, transparent, rgba(255,255,255,.34), transparent);
}
.day-carousel .day-title {
  color: var(--header-text);
  text-shadow: 0 1px 2px rgba(9, 16, 43, .24);
}
.day-carousel .day-panel[data-position="previous"] .day-title,
.day-carousel .day-panel[data-position="next"] .day-title {
  color: var(--header-muted);
}
.header-control,
html[data-theme="dark"] .header-control {
  color: #ffffff;
  border-color: var(--header-control-line);
  background: var(--header-control-bg);
  box-shadow: 0 7px 18px rgba(9, 18, 49, .19), inset 0 1px 0 rgba(255,255,255,.20);
  backdrop-filter: blur(12px) saturate(115%);
}
.header-control:hover,
html[data-theme="dark"] .header-control:hover {
  color: #ffffff;
  border-color: rgba(255,255,255,.48);
  background: var(--header-control-hover);
}
.live-dot,
html[data-theme="dark"] .live-dot { color: var(--header-live); }
.live-dot::before {
  box-shadow: 0 0 0 4px rgba(201, 255, 241, .15);
}

/* Daily Panchang opt-in: one clear decision, no competing copy. */
.daily-prompt {
  width: min(88vw, 370px); margin: auto; padding: 0; overflow: visible;
  border: 1px solid rgba(63, 75, 128, .20); border-radius: 24px;
  color: var(--text); background:
    radial-gradient(110% 95% at 0% 0%, rgba(255, 220, 137, .20), transparent 52%),
    radial-gradient(95% 100% at 100% 100%, rgba(72, 177, 177, .13), transparent 56%),
    var(--surface-strong);
  box-shadow: 0 28px 90px rgba(25, 34, 68, .30);
}
html[data-theme="dark"] .daily-prompt {
  border-color: rgba(158, 174, 236, .24);
  background:
    radial-gradient(110% 95% at 0% 0%, rgba(245, 193, 82, .12), transparent 52%),
    radial-gradient(95% 100% at 100% 100%, rgba(62, 174, 177, .12), transparent 56%),
    #111a32;
  box-shadow: 0 30px 100px rgba(0, 0, 0, .62);
}
.daily-prompt::backdrop {
  background: rgba(24, 31, 54, .38);
  backdrop-filter: blur(9px) saturate(.86);
}
.daily-prompt-card {
  position: relative; display: grid; justify-items: center; gap: 18px;
  padding: 30px 24px 23px; text-align: center;
}
.daily-prompt-close {
  position: absolute; z-index: 2; top: 9px; right: 9px; width: 30px; height: 30px;
  display: grid; place-items: center; border: 1px solid var(--line); border-radius: 50%;
  color: var(--muted); background: rgba(255,255,255,.62); cursor: pointer;
  font: 500 20px/1 inherit; transition: transform .15s ease, background .15s ease, color .15s ease;
}
html[data-theme="dark"] .daily-prompt-close { background: rgba(255,255,255,.07); }
.daily-prompt-close:hover { color: var(--text); background: var(--surface-muted); transform: rotate(4deg); }
.daily-prompt-mark {
  width: 54px; aspect-ratio: 1; display: grid; place-items: center; border-radius: 17px;
  color: #ffffff; background: linear-gradient(145deg, var(--header-mid), var(--header-end));
  box-shadow: 0 12px 28px rgba(55, 76, 151, .22), inset 0 1px 0 rgba(255,255,255,.28);
  font-size: 25px; line-height: 1;
}
.daily-prompt h2 {
  max-width: 300px; margin: 0; padding-block: .08em; color: var(--text);
  font-size: clamp(21px, 5.4vw, 27px); line-height: 1.28; font-weight: 650;
  letter-spacing: -.026em; text-wrap: balance;
}
.daily-prompt-yes {
  width: 100%; min-height: 49px; border: 1px solid rgba(47, 72, 154, .36); border-radius: 14px;
  color: #ffffff; background: linear-gradient(112deg, var(--header-start), var(--header-mid) 55%, var(--header-end));
  box-shadow: 0 10px 24px rgba(43, 61, 130, .20); cursor: pointer;
  font: 650 16px/1.2 inherit; letter-spacing: -.006em;
  transition: transform .15s ease, filter .15s ease, box-shadow .15s ease;
}
.daily-prompt-yes:hover { filter: brightness(1.05); transform: translateY(-1px); box-shadow: 0 13px 28px rgba(43, 61, 130, .24); }
.daily-prompt-yes:active { transform: translateY(1px); }
.daily-prompt-yes:disabled { cursor: wait; opacity: .72; transform: none; }
.daily-prompt-yes:focus-visible, .daily-prompt-close:focus-visible { outline: 3px solid rgba(72, 91, 202, .28); outline-offset: 3px; }

@media (max-width: 380px) {
  .daily-prompt-card { gap: 15px; padding: 27px 18px 18px; }
  .daily-prompt-mark { width: 48px; border-radius: 15px; font-size: 22px; }
}

@media (prefers-reduced-motion: reduce) {
  *, *::before, *::after { animation-duration: .001ms !important; animation-iteration-count: 1 !important; scroll-behavior: auto !important; transition-duration: .001ms !important; }
}

@media (forced-colors: active) {
  .moment, .metric-row, .day-carousel, .fab, .header-control, .settings-sheet, .daily-prompt { border: 1px solid CanvasText; }
  .badge { border: 1px solid CanvasText; }
}

/* Stable editor: vertical scrolling only, no sideways movement or width jump. */
.settings-sheet {
  overflow: hidden;
  max-width: calc(100vw - 18px);
}
.settings-form,
.sheet-head,
.sheet-body,
.sheet-actions,
.field,
.form-grid,
.switch-row,
.share-preview,
.seo-copy {
  min-width: 0;
  max-width: 100%;
  box-sizing: border-box;
}
.settings-form { width: 100%; overflow: hidden; }
.sheet-body {
  width: 100%;
  overflow-x: hidden;
  overflow-y: auto;
  scrollbar-gutter: stable;
  overscroll-behavior-x: none;
  touch-action: pan-y;
}
.input-shell,
.input-shell input,
.field input,
.field select,
.location-button,
.share-preview-frame,
.share-preview-frame img { min-width: 0; max-width: 100%; box-sizing: border-box; }
.share-preview-frame { overflow: hidden; aspect-ratio: 1200 / 630; }
.date-picker-shell {
  position: relative;
  width: 100%;
  height: 38px;
  display: flex;
  align-items: center;
  border: 1px solid var(--line-strong);
  border-radius: 9px;
  color: var(--text);
  background: var(--surface-muted);
  overflow: hidden;
  transition: border-color .15s ease, box-shadow .15s ease, background .15s ease;
}
.date-picker-shell:focus-within {
  border-color: rgba(67, 84, 196, .68);
  box-shadow: 0 0 0 4px rgba(67, 84, 196, .11);
  background: var(--surface-strong);
}
.date-display {
  min-width: 0;
  flex: 1;
  padding-inline: 10px 34px;
  font-size: 13.5px;
  line-height: 1;
  font-weight: 400;
  font-variant-numeric: tabular-nums;
  white-space: nowrap;
  overflow: hidden;
  text-overflow: ellipsis;
  pointer-events: none;
}
.date-picker-icon {
  position: absolute;
  inset-inline-end: 11px;
  top: 50%;
  transform: translateY(-50%);
  color: var(--muted);
  font-size: 15px;
  line-height: 1;
  pointer-events: none;
}
.date-picker-shell .date-native-input {
  position: absolute;
  z-index: 2;
  inset: 0;
  width: 100%;
  height: 100%;
  margin: 0;
  padding: 0;
  border: 0;
  border-radius: inherit;
  opacity: 0;
  cursor: pointer;
  background: transparent;
}
.seo-copy {
  margin: 3px 0 1px;
  padding: 10px 11px;
  border: 1px solid var(--line);
  border-radius: 10px;
  color: var(--muted);
  background: color-mix(in srgb, var(--surface-muted) 78%, transparent);
  font-size: 10.75px;
  line-height: 1.55;
  font-weight: 400;
  letter-spacing: 0;
  overflow-wrap: anywhere;
  word-break: normal;
  text-align: start;
}
html[data-theme="dark"] .seo-copy { background: rgba(255,255,255,.035); }

@media (max-width: 560px) {
  .settings-sheet { width: calc(100vw - 20px); }
  .seo-copy { font-size: 10.5px; line-height: 1.5; }
}
"""

JS = r"""
(() => {
  'use strict';

  const initialNode = document.getElementById('initial-data');
  let state = JSON.parse(initialNode.textContent);
  const pushConfig = Object.freeze({...((state && state.push) || {})});
  const DAILY_VISIT_KEY = 'panchang-last-visit-v1';
  const DAILY_PUSH_KEY = 'panchang-daily-push-v1';
  let shouldOfferDailyPanchang = false;
  try {
    const now = Date.now();
    const previousVisit = Number(localStorage.getItem(DAILY_VISIT_KEY) || 0);
    const days = Math.max(1, Number(pushConfig.offer_after_days || 7));
    shouldOfferDailyPanchang = !previousVisit || now - previousVisit >= days * 86400000;
    localStorage.setItem(DAILY_VISIT_KEY, String(now));
  } catch (_) {
    try {
      shouldOfferDailyPanchang = !sessionStorage.getItem(DAILY_VISIT_KEY);
      sessionStorage.setItem(DAILY_VISIT_KEY, '1');
    } catch (_) {
      shouldOfferDailyPanchang = true;
    }
  }
  let settings = {
    place: state.query.place,
    slug: state.query.slug,
    lat: state.query.lat,
    lon: state.query.lon,
    timezone: state.query.timezone,
    date: state.query.date,
    time: state.query.time,
    language: state.query.language,
    live: state.query.live !== false,
    theme: document.documentElement.dataset.theme === 'dark' ? 'dark' : 'light',
    country: state.query.country || '',
    locationMode: 'server'
  };
  try {
    const initialParts = new Intl.DateTimeFormat('en-CA', {
      timeZone: settings.timezone, year: 'numeric', month: '2-digit', day: '2-digit'
    }).formatToParts(new Date());
    const initialValues = Object.fromEntries(initialParts.filter(part => part.type !== 'literal').map(part => [part.type, part.value]));
    settings.followToday = settings.date === `${initialValues.year}-${initialValues.month}-${initialValues.day}`;
  } catch (_) {
    settings.followToday = true;
  }
  let loading = false;
  let selectedPlace = true;
  let selectWholePlaceOnPointer = true;
  let placeMatches = [];
  let dayScrollTimer = 0;
  let suppressDayScroll = true;
  let searchTimer = 0;
  let toastTimer = 0;
  let lastDataFetch = Date.now();
  let lastLiveMinute = '';
  let lastDataMinute = `${settings.date}T${settings.time}`;
  let minuteRefreshTimer = 0;
  let minuteRefreshRetryTimer = 0;
  let dailyPromptTimer = 0;
  let serviceWorkerRegistrationPromise = null;
  let pushSyncPromise = null;
  let lastPushSyncAt = 0;

  const $ = (selector, root = document) => root.querySelector(selector);
  const $$ = (selector, root = document) => Array.from(root.querySelectorAll(selector));
  const metrics = $('#metrics');
  const dataRows = $('#dataRows');
  const dayRail = $('#dayRail');
  const dialog = $('#settingsDialog');
  const form = $('#settingsForm');
  const placeInput = $('#placeInput');
  const placeResults = $('#placeResults');
  const dateInput = $('#dateInput');
  const dateDisplay = $('#dateDisplay');
  const timeInput = $('#timeInput');
  const languageInput = $('#languageInput');
  const liveInput = $('#liveInput');
  const editButton = $('#editButton');
  const closeButton = $('#closeDialog');
  const cancelButton = $('#cancelButton');
  const locationButton = $('#locationButton');
  const previousDayButton = $('#previousDayButton');
  const nextDayButton = $('#nextDayButton');
  const toastNode = $('#toast');
  const loadingMask = $('#loadingMask');
  const liveIndicator = $('#liveIndicator');
  const ldJsonNode = $('#structuredData');
  const ogPreviewImage = $('#ogPreviewImage');
  const seoCopyNode = $('#seoCopy');
  const themeToggleButton = $('#themeToggleButton');
  const dailyPrompt = $('#dailyPrompt');
  const dailyPromptClose = $('#dailyPromptClose');
  const dailyPromptYes = $('#dailyPromptYes');

  const cssEscape = window.CSS && typeof window.CSS.escape === 'function'
    ? window.CSS.escape.bind(window.CSS)
    : value => String(value).replace(/[^a-zA-Z0-9_-]/g, char => `\${char}`);

  const localeMap = {
    en: 'en-IN', hi: 'hi-IN', mr: 'mr-IN', gu: 'gu-IN', bn: 'bn-IN', ta: 'ta-IN',
    te: 'te-IN', kn: 'kn-IN', ml: 'ml-IN', pa: 'pa-IN', or: 'or-IN', ne: 'ne-NP', sa: 'sa-IN'
  };

  function readableIsoDate(isoDate, language = settings.language) {
    const values = String(isoDate || '').split('-').map(Number);
    if (values.length !== 3 || values.some(value => !Number.isFinite(value))) return String(isoDate || '');
    const [year, month, day] = values;
    const languageMonths = state.month_names?.[language];
    const months = Array.isArray(languageMonths) && languageMonths.length === 12
      ? languageMonths
      : (Array.isArray(state.months) && state.months.length === 12
        ? state.months
        : ['Jan', 'Feb', 'Mar', 'Apr', 'May', 'Jun', 'Jul', 'Aug', 'Sept', 'Oct', 'Nov', 'Dec']);
    return `${day} ${months[Math.max(0, Math.min(11, month - 1))]} ${year}`;
  }

  function syncDateDisplay() {
    if (!dateDisplay) return;
    dateDisplay.textContent = readableIsoDate(dateInput?.value || settings.date, languageInput?.value || settings.language);
    dateDisplay.lang = languageInput?.value || settings.language;
  }

  function escapeHtml(value) {
    return String(value ?? '')
      .replaceAll('&', '&amp;').replaceAll('<', '&lt;').replaceAll('>', '&gt;')
      .replaceAll('"', '&quot;').replaceAll("'", '&#039;');
  }

  function showToast(message) {
    window.clearTimeout(toastTimer);
    toastNode.textContent = message;
    toastNode.classList.add('show');
    toastTimer = window.setTimeout(() => toastNode.classList.remove('show'), 3200);
  }

  function isIosDevice() {
    return /iPad|iPhone|iPod/.test(navigator.userAgent) || (navigator.platform === 'MacIntel' && navigator.maxTouchPoints > 1);
  }

  function isStandaloneApp() {
    return window.matchMedia?.('(display-mode: standalone)').matches || navigator.standalone === true;
  }

  function dailyPushCanBeOffered() {
    if (!pushConfig.enabled || !pushConfig.public_key || !window.isSecureContext) return false;
    if (!('serviceWorker' in navigator) || !('Notification' in window)) return false;
    return 'PushManager' in window || isIosDevice();
  }

  function urlBase64ToUint8Array(value) {
    const padding = '='.repeat((4 - value.length % 4) % 4);
    const base64 = (value + padding).replaceAll('-', '+').replaceAll('_', '/');
    const raw = window.atob(base64);
    return Uint8Array.from([...raw].map(character => character.charCodeAt(0)));
  }

  function ensureServiceWorker() {
    if (!('serviceWorker' in navigator)) return Promise.reject(new Error('Service workers are unavailable'));
    if (!serviceWorkerRegistrationPromise) {
      serviceWorkerRegistrationPromise = navigator.serviceWorker.register('/sw.js')
        .then(() => navigator.serviceWorker.ready)
        .catch(error => {
          serviceWorkerRegistrationPromise = null;
          throw error;
        });
    }
    return serviceWorkerRegistrationPromise;
  }

  function deviceTimezone() {
    try {
      return Intl.DateTimeFormat().resolvedOptions().timeZone || settings.timezone || 'UTC';
    } catch (_) {
      return settings.timezone || 'UTC';
    }
  }

  function dailyNotificationTargetUrl() {
    const params = new URLSearchParams({
      place: settings.place,
      lat: String(settings.lat),
      lon: String(settings.lon),
      tz: settings.timezone,
      lang: settings.language,
      live: '1'
    });
    if (settings.country) params.set('country', settings.country);
    return `/?${params.toString()}`;
  }

  async function storePushSubscription(subscription) {
    const response = await fetch('/api/push/subscribe', {
      method: 'POST',
      headers: {
        'Accept': 'application/json',
        'Content-Type': 'application/json',
        'X-Panchang-CSRF': pushConfig.csrf || ''
      },
      credentials: 'same-origin',
      cache: 'no-store',
      body: JSON.stringify({
        subscription: subscription.toJSON(),
        language: settings.language,
        timezone: deviceTimezone(),
        target_url: dailyNotificationTargetUrl()
      })
    });
    if (!response.ok) {
      const detail = await response.json().catch(() => ({}));
      throw new Error(detail.error || `Push subscription failed: ${response.status}`);
    }
    return response.json();
  }

  async function syncDailyPushSubscription({force = false} = {}) {
    if (!dailyPushCanBeOffered() || Notification.permission !== 'granted' || !('PushManager' in window)) return false;
    if (!force && Date.now() - lastPushSyncAt < 3600000) return true;
    if (pushSyncPromise) return pushSyncPromise;
    pushSyncPromise = (async () => {
      const registration = await ensureServiceWorker();
      const subscription = await registration.pushManager.getSubscription();
      if (!subscription) return false;
      await storePushSubscription(subscription);
      lastPushSyncAt = Date.now();
      try { localStorage.setItem(DAILY_PUSH_KEY, '1'); } catch (_) { /* Storage is optional. */ }
      return true;
    })().catch(error => {
      console.warn('Daily Panchang push sync failed', error);
      return false;
    }).finally(() => { pushSyncPromise = null; });
    return pushSyncPromise;
  }

  function closeDailyPrompt() {
    window.clearTimeout(dailyPromptTimer);
    if (!dailyPrompt) return;
    if (typeof dailyPrompt.close === 'function' && dailyPrompt.open) dailyPrompt.close();
    else dailyPrompt.removeAttribute('open');
  }

  function scheduleDailyPrompt(delay = 1800) {
    window.clearTimeout(dailyPromptTimer);
    dailyPromptTimer = window.setTimeout(() => maybeOfferDailyPanchang(), delay);
  }

  async function maybeOfferDailyPanchang() {
    if (!shouldOfferDailyPanchang || !dailyPrompt || !dailyPushCanBeOffered()) return;
    if (Notification.permission === 'denied') return;
    if (document.visibilityState !== 'visible' || dialog.open) {
      scheduleDailyPrompt(1800);
      return;
    }
    try {
      if ('PushManager' in window) {
        const registration = await ensureServiceWorker();
        const existing = await registration.pushManager.getSubscription();
        if (existing) {
          await syncDailyPushSubscription({force: true});
          return;
        }
      }
    } catch (error) {
      console.warn('Could not inspect push subscription', error);
    }
    if (typeof dailyPrompt.showModal === 'function') dailyPrompt.showModal();
    else dailyPrompt.setAttribute('open', '');
  }

  async function enableDailyPanchang() {
    if (!dailyPromptYes) return;
    dailyPromptYes.disabled = true;
    try {
      if (isIosDevice() && !isStandaloneApp()) {
        closeDailyPrompt();
        showToast(state.ui.notification_install_hint || state.ui.notification_unavailable);
        return;
      }
      if (!dailyPushCanBeOffered() || !('PushManager' in window)) {
        closeDailyPrompt();
        showToast(state.ui.notification_unavailable);
        return;
      }
      const permission = Notification.permission === 'granted'
        ? 'granted'
        : await Notification.requestPermission();
      if (permission !== 'granted') {
        closeDailyPrompt();
        showToast(state.ui.notification_blocked);
        return;
      }
      const registration = await ensureServiceWorker();
      let subscription = await registration.pushManager.getSubscription();
      if (!subscription) {
        subscription = await registration.pushManager.subscribe({
          userVisibleOnly: true,
          applicationServerKey: urlBase64ToUint8Array(pushConfig.public_key)
        });
      }
      await storePushSubscription(subscription);
      lastPushSyncAt = Date.now();
      shouldOfferDailyPanchang = false;
      try { localStorage.setItem(DAILY_PUSH_KEY, '1'); } catch (_) { /* Storage is optional. */ }
      closeDailyPrompt();
      showToast(state.ui.notification_enabled);
    } catch (error) {
      console.error('Daily Panchang notification setup failed', error);
      showToast(state.ui.notification_error);
    } finally {
      dailyPromptYes.disabled = false;
    }
  }

  dailyPromptYes?.addEventListener('click', enableDailyPanchang);
  dailyPromptClose?.addEventListener('click', closeDailyPrompt);
  dailyPrompt?.addEventListener('cancel', event => {
    event.preventDefault();
    closeDailyPrompt();
  });
  dailyPrompt?.addEventListener('click', event => {
    if (event.target === dailyPrompt) closeDailyPrompt();
  });

  function updateThemeToggle() {
    if (!themeToggleButton) return;
    const isDark = settings.theme === 'dark';
    const label = isDark ? state.ui.dark_theme : state.ui.light_theme;
    const glyph = isDark ? '◐' : '☀';
    themeToggleButton.innerHTML = `<span class="theme-glyph" aria-hidden="true">${glyph}</span><span>${escapeHtml(label)}</span>`;
    themeToggleButton.setAttribute('aria-label', `${state.ui.appearance}: ${label}`);
    themeToggleButton.setAttribute('aria-pressed', String(isDark));
  }

  function applyTheme(theme, {persist = true} = {}) {
    const normalized = theme === 'dark' ? 'dark' : 'light';
    settings.theme = normalized;
    document.documentElement.dataset.theme = normalized;
    document.documentElement.style.colorScheme = normalized;
    const themeColor = $('meta[name="theme-color"]');
    const colorScheme = $('meta[name="color-scheme"]');
    if (themeColor) themeColor.content = normalized === 'dark' ? '#1b294f' : '#35498f';
    if (colorScheme) colorScheme.content = normalized;
    updateThemeToggle();
    if (persist) {
      try { localStorage.setItem('panchang-theme', normalized); } catch (_) { /* Storage is optional. */ }
    }
  }

  themeToggleButton?.addEventListener('click', () => {
    applyTheme(settings.theme === 'dark' ? 'light' : 'dark');
  });

  function renderMoment(item) {
    const classes = [
      'moment',
      item.quality || 'neutral',
      item.detail && item.detail === state.ui.mixed ? 'mixed' : '',
      item.current ? 'is-current' : '',
      item.starts_day ? 'starts-day' : ''
    ].filter(Boolean).join(' ');
    const currentAttr = item.current ? ' aria-current="true"' : '';
    const datetimeAttr = item.start ? ` datetime="${escapeHtml(item.start)}"` : '';
    const endDatetimeAttr = item.end ? ` datetime="${escapeHtml(item.end)}"` : '';
    const dateText = item.date || '';
    const clockText = item.clock || item.time || '';
    const crossesDay = Boolean(item.crosses_day && item.start_display && item.end_display);
    const timingMarkup = crossesDay
      ? `<time class="moment-date moment-endpoint"${datetimeAttr}>${escapeHtml(item.start_display)}</time><time class="moment-time moment-endpoint moment-endpoint-end"${endDatetimeAttr}>→ ${escapeHtml(item.end_display)}</time>`
      : `<span class="moment-date">${escapeHtml(dateText)}</span><time class="moment-time"${datetimeAttr}>${escapeHtml(clockText)}</time>`;
    const width = Math.max(1, Number(item.width_px) || 280);
    const mobileWidth = Math.max(1, Number(item.mobile_width_px) || width);
    const landscapeWidth = Math.max(1, Number(item.landscape_width_px) || width);
    const duration = Math.max(1, Number(item.duration_minutes) || 1);
    const style = `--duration-width:${width}px;--duration-width-mobile:${mobileWidth}px;--duration-width-landscape:${landscapeWidth}px`;
    const ariaTiming = item.time || `${dateText}. ${clockText}`;
    const aria = `${item.title}. ${ariaTiming}. ${item.quality === 'auspicious' ? state.ui.good : item.quality === 'inauspicious' ? state.ui.avoid : ''}`;
    return `
      <article class="${classes}" style="${style}" data-duration-minutes="${duration}" data-day-key="${escapeHtml(item.day_key || '')}" role="listitem"${currentAttr} aria-label="${escapeHtml(aria)}">
        <span class="moment-title" itemprop="value">${escapeHtml(item.title)}</span>
        <span class="moment-meta">${timingMarkup}</span>
      </article>`;
  }

  function captureTimelineState() {
    const snapshot = {};
    $$('.metric-row', metrics).forEach(row => {
      const rail = $('.timeline', row);
      if (!rail) return;
      const current = $('.moment.is-current', rail);
      const currentLeft = current ? current.offsetLeft : Number.NaN;
      snapshot[row.dataset.section] = {
        scrollLeft: rail.scrollLeft,
        nearCurrent: Number.isFinite(currentLeft) && Math.abs(rail.scrollLeft - currentLeft) <= Math.max(24, current.offsetWidth * .18)
      };
    });
    return snapshot;
  }

  function restoreTimelineState(snapshot) {
    $$('.metric-row', metrics).forEach(row => {
      const rail = $('.timeline', row);
      const saved = snapshot?.[row.dataset.section];
      if (!rail || !saved) return;
      const current = $('.moment.is-current', rail);
      if (saved.nearCurrent && current) {
        rail.scrollLeft = current.offsetLeft;
      } else {
        rail.scrollLeft = Math.min(saved.scrollLeft, Math.max(0, rail.scrollWidth - rail.clientWidth));
      }
    });
  }

  function renderSections(timelineState = null) {
    dataRows.innerHTML = state.sections.map(section => `
      <section class="metric-row" data-section="${escapeHtml(section.key)}" itemscope itemtype="https://schema.org/Observation">
        <div class="metric-label">
          <span class="metric-icon" aria-hidden="true">${escapeHtml(section.icon)}</span>
          <h2 itemprop="variableMeasured">${escapeHtml(section.label)}</h2>
        </div>
        <div class="timeline-wrap">
          <div class="timeline" tabindex="0" role="list" aria-label="${escapeHtml(section.label)} — ${escapeHtml(state.ui.timeline_hint)}">
            ${section.items.map(renderMoment).join('')}
          </div>
        </div>
      </section>`).join('');
    bindTimelineInteractions();
    requestAnimationFrame(() => timelineState ? restoreTimelineState(timelineState) : centerCurrentItems());
  }

  function bindTimelineInteractions() {
    $$('.timeline', metrics).forEach(rail => {
      rail.addEventListener('wheel', event => {
        if (Math.abs(event.deltaY) > Math.abs(event.deltaX)) {
          event.preventDefault();
          rail.scrollLeft += event.deltaY;
        }
      }, {passive: false});
      rail.addEventListener('keydown', event => {
        if (!['ArrowLeft', 'ArrowRight', 'Home', 'End'].includes(event.key)) return;
        event.preventDefault();
        const amount = Math.max(160, rail.clientWidth * .72);
        if (event.key === 'ArrowLeft') rail.scrollBy({left: -amount, behavior: 'smooth'});
        if (event.key === 'ArrowRight') rail.scrollBy({left: amount, behavior: 'smooth'});
        if (event.key === 'Home') rail.scrollTo({left: 0, behavior: 'smooth'});
        if (event.key === 'End') rail.scrollTo({left: rail.scrollWidth, behavior: 'smooth'});
      });
    });
  }

  function centerCurrentItems() {
    $$('.timeline', metrics).forEach(rail => {
      const current = $('.moment.is-current', rail);
      if (!current) return;
      rail.scrollLeft = current.offsetLeft;
    });
  }

  function renderDayRail() {
    const compact = state.headers_compact || state.headers;
    dayRail.innerHTML = [
      ['previous', state.headers.previous, compact.previous],
      ['current', state.headers.current, compact.current],
      ['next', state.headers.next, compact.next]
    ].map(([position, text, compactText]) => `
      <div class="day-panel" data-position="${position}" aria-label="${escapeHtml(position === 'previous' ? state.ui.previous_day : position === 'next' ? state.ui.next_day : state.ui.selected_day)}">
        ${position === 'current'
          ? `<h1 class="day-title" id="currentHeaderText"><span class="header-full">${escapeHtml(text)}</span><span class="header-compact">${escapeHtml(compactText)}</span></h1>`
          : `<span class="day-title"><span class="header-full">${escapeHtml(text)}</span><span class="header-compact">${escapeHtml(compactText)}</span></span>`}
      </div>`).join('');
    suppressDayScroll = true;
    requestAnimationFrame(() => {
      centerDayRail();
      fitHeaderText();
      window.setTimeout(() => { suppressDayScroll = false; }, 90);
    });
    liveIndicator.hidden = !settings.live;
  }

  function centerDayRail() {
    const currentPanel = $('.day-panel[data-position="current"]', dayRail);
    dayRail.scrollLeft = currentPanel ? currentPanel.offsetLeft : dayRail.clientWidth;
  }

  function fitHeaderText() {
    const minimum = window.innerWidth <= 360 ? 9.5 : window.innerWidth <= 560 ? 10.5 : 14;
    $$('.day-title', dayRail).forEach(node => {
      node.style.fontSize = '';
      const maximum = parseFloat(getComputedStyle(node).fontSize) || 24;
      let low = minimum;
      let high = maximum;
      for (let i = 0; i < 9; i += 1) {
        const mid = (low + high) / 2;
        node.style.fontSize = `${mid}px`;
        if (node.scrollWidth <= node.clientWidth) low = mid;
        else high = mid;
      }
      node.style.fontSize = `${Math.max(minimum, low - .1)}px`;
    });
  }

  function applyI18n() {
    document.documentElement.lang = settings.language;
    $$('[data-i18n]').forEach(node => {
      const key = node.dataset.i18n;
      if (state.ui[key]) node.textContent = state.ui[key];
    });
    $$('[data-i18n-placeholder]').forEach(node => {
      const key = node.dataset.i18nPlaceholder;
      if (state.ui[key]) node.setAttribute('placeholder', state.ui[key]);
    });
    editButton.dataset.tooltip = state.ui.edit;
    editButton.setAttribute('aria-label', state.ui.edit);
    closeButton.setAttribute('aria-label', state.ui.close);
    if (dailyPromptClose) dailyPromptClose.setAttribute('aria-label', state.ui.close);
    previousDayButton.setAttribute('aria-label', state.ui.previous_day);
    nextDayButton.setAttribute('aria-label', state.ui.next_day);
    liveIndicator.textContent = state.ui.live;
    updateThemeToggle();
  }

  function previewImageUrl() {
    const language = languageInput?.value || settings.language || 'en';
    const isLive = liveInput?.checked ?? settings.live;
    const parts = getZonedParts(settings.timezone);
    const currentDate = `${parts.year}-${String(parts.month).padStart(2, '0')}-${String(parts.day).padStart(2, '0')}`;
    const currentTime = `${String(parts.hour).padStart(2, '0')}:${String(parts.minute).padStart(2, '0')}`;
    const selectedDate = isLive ? currentDate : (dateInput?.value || settings.date);
    const selectedTime = isLive ? currentTime : (timeInput?.value || settings.time || currentTime);
    const snapshot = `${selectedDate.replaceAll('-', '')}${selectedTime.replace(':', '')}`;
    const params = new URLSearchParams({
      place: settings.place, lat: String(settings.lat), lon: String(settings.lon), tz: settings.timezone,
      date: selectedDate, time: selectedTime, lang: language, live: isLive ? '1' : '0', v: state.app?.version || '1'
    });
    if (settings.country) params.set('country', settings.country);
    return `/og/${encodeURIComponent(language)}/${snapshot}.png?${params.toString()}`;
  }

  function updateOgPreview(url = '') {
    if (!ogPreviewImage) return;
    const nextUrl = url || previewImageUrl();
    if (ogPreviewImage.getAttribute('src') !== nextUrl) {
      ogPreviewImage.setAttribute('aria-busy', 'true');
      ogPreviewImage.src = nextUrl;
    }
    ogPreviewImage.alt = state.seo?.image_alt || state.ui.share_image_alt || state.ui.panchang;
  }

  if (ogPreviewImage) {
    ogPreviewImage.addEventListener('load', () => ogPreviewImage.removeAttribute('aria-busy'));
    ogPreviewImage.addEventListener('error', () => ogPreviewImage.removeAttribute('aria-busy'));
  }

  function renderSeo() {
    if (!state.seo) return;
    document.title = state.seo.title;
    const description = $('meta[name="description"]');
    if (description) description.content = state.seo.description;
    const abstractMeta = $('meta[name="abstract"]');
    if (abstractMeta) abstractMeta.content = state.seo.copy || '';
    const keywords = $('meta[name="keywords"]');
    if (keywords) keywords.content = state.seo.keywords || '';
    if (seoCopyNode) {
      seoCopyNode.textContent = state.seo.copy || '';
      seoCopyNode.lang = settings.language;
    }
    const canonical = $('link[rel="canonical"]');
    if (canonical) canonical.href = state.seo.canonical;
    const ogTitle = $('meta[property="og:title"]');
    const ogDescription = $('meta[property="og:description"]');
    const ogUrl = $('meta[property="og:url"]');
    const ogImage = $('meta[property="og:image"]');
    const ogImageUrl = $('meta[property="og:image:url"]');
    const ogSecureImage = $('meta[property="og:image:secure_url"]');
    const ogImageAlt = $('meta[property="og:image:alt"]');
    const imageSrc = $('link[rel="image_src"]');
    const itempropImage = $('meta[itemprop="image"]');
    const twitterTitle = $('meta[name="twitter:title"]');
    const twitterDescription = $('meta[name="twitter:description"]');
    const twitterImage = $('meta[name="twitter:image"]');
    const twitterImageSrc = $('meta[name="twitter:image:src"]');
    const twitterImageAlt = $('meta[name="twitter:image:alt"]');
    if (ogTitle) ogTitle.content = state.seo.title;
    if (ogDescription) ogDescription.content = state.seo.description;
    if (ogUrl) ogUrl.content = state.seo.canonical;
    if (ogImage) ogImage.content = state.seo.og_image;
    if (ogImageUrl) ogImageUrl.content = state.seo.og_image;
    if (ogSecureImage) ogSecureImage.content = state.seo.og_image;
    if (ogImageAlt) ogImageAlt.content = state.seo.image_alt || state.seo.title;
    if (imageSrc) imageSrc.href = state.seo.og_image;
    if (itempropImage) itempropImage.content = state.seo.og_image;
    if (twitterTitle) twitterTitle.content = state.seo.title;
    if (twitterDescription) twitterDescription.content = state.seo.description;
    if (twitterImage) twitterImage.content = state.seo.og_image;
    if (twitterImageSrc) twitterImageSrc.content = state.seo.og_image;
    if (twitterImageAlt) twitterImageAlt.content = state.seo.image_alt || state.seo.title;
    updateOgPreview(state.seo.og_image);
    Object.entries(state.seo.alternates || {}).forEach(([code, href]) => {
      let link = $(`link[rel="alternate"][hreflang="${cssEscape(code)}"]`);
      if (!link) {
        link = document.createElement('link');
        link.rel = 'alternate';
        link.hreflang = code;
        document.head.appendChild(link);
      }
      link.href = href;
    });
    if (state.jsonld && ldJsonNode) ldJsonNode.textContent = JSON.stringify(state.jsonld);
  }

  function renderAll({timelineState = null} = {}) {
    applyTheme(settings.theme, {persist: false});
    applyI18n();
    renderDayRail();
    renderSections(timelineState);
    renderSeo();
    syncForm();
  }

  function addDays(isoDate, amount) {
    const [year, month, day] = isoDate.split('-').map(Number);
    const value = new Date(Date.UTC(year, month - 1, day + amount, 12));
    return `${value.getUTCFullYear()}-${String(value.getUTCMonth() + 1).padStart(2, '0')}-${String(value.getUTCDate()).padStart(2, '0')}`;
  }

  function apiRequestUrl() {
    const params = new URLSearchParams({
      place: settings.place,
      lat: String(settings.lat),
      lon: String(settings.lon),
      tz: settings.timezone,
      lang: settings.language,
      live: settings.live ? '1' : '0',
      _: String(Date.now())
    });
    if (!settings.live) {
      params.set('date', settings.date);
      params.set('time', settings.time);
    }
    if (settings.country) params.set('country', settings.country);
    return `/api/panchang?${params.toString()}`;
  }

  function animationDone(animation) {
    return animation ? animation.finished.catch(() => undefined) : Promise.resolve();
  }

  async function fetchPanchang(direction = 0, historyMode = 'push', {timelineState = null, showMask = true} = {}) {
    if (loading) return false;
    if (settings.live) {
      settings.followToday = true;
      applyCurrentZonedTime({updateDate: true});
    }
    liveInput.checked = settings.live;
    loading = true;
    const locationMode = settings.locationMode || 'server';
    metrics.classList.add('is-busy');
    metrics.setAttribute('aria-busy', 'true');
    const maskTimer = showMask ? window.setTimeout(() => loadingMask.classList.add('show'), 180) : 0;
    const outAnimation = direction ? metrics.animate([
      {transform: 'translateX(0)', opacity: 1},
      {transform: `translateX(${direction > 0 ? '-7%' : '7%'})`, opacity: .18}
    ], {duration: 145, easing: 'ease-in', fill: 'forwards'}) : null;

    try {
      const responsePromise = fetch(apiRequestUrl(), {headers: {'Accept': 'application/json'}, cache: 'no-store'});
      const [response] = await Promise.all([responsePromise, animationDone(outAnimation)]);
      if (!response.ok) throw new Error(`HTTP ${response.status}`);
      const nextState = await response.json();
      if (nextState.error) throw new Error(nextState.error);
      state = nextState;
      settings = {
        place: state.query.place,
        slug: state.query.slug,
        lat: state.query.lat,
        lon: state.query.lon,
        timezone: state.query.timezone,
        date: state.query.date,
        time: state.query.time,
        language: state.query.language,
        live: state.query.live !== false,
        theme: settings.theme,
        followToday: state.query.live !== false ? settings.followToday : false,
        country: state.query.country || '',
        locationMode
      };
      renderAll({timelineState});
      if (direction) {
        metrics.animate([
          {transform: `translateX(${direction > 0 ? '7%' : '-7%'})`, opacity: .16},
          {transform: 'translateX(0)', opacity: 1}
        ], {duration: 190, easing: 'cubic-bezier(.2,.8,.2,1)'});
      }
      lastDataFetch = Date.now();
      lastDataMinute = `${settings.date}T${settings.time}`;
      savePreferences();
      updateHistory(historyMode);
      syncDailyPushSubscription().catch(() => undefined);
      return true;
    } catch (error) {
      console.error(error);
      showToast(state.ui.load_error);
      renderDayRail();
      return false;
    } finally {
      if (maskTimer) window.clearTimeout(maskTimer);
      loadingMask.classList.remove('show');
      metrics.classList.remove('is-busy');
      metrics.setAttribute('aria-busy', 'false');
      if (outAnimation) outAnimation.cancel();
      loading = false;
    }
  }

  function updateHistory(mode = 'push') {
    if (!state.seo?.canonical) return;
    const target = new URL(state.seo.canonical, location.origin);
    const params = target.searchParams;
    params.set('live', settings.live ? '1' : '0');
    if (settings.live) params.delete('time');
    else params.set('time', settings.time);
    const localUrl = `${target.pathname}${params.toString() ? `?${params.toString()}` : ''}`;
    const method = mode === 'replace' ? 'replaceState' : 'pushState';
    history[method]({panchang: true}, '', localUrl);
  }

  async function shiftDay(direction) {
    if (loading || ![-1, 1].includes(direction)) return;
    settings.date = addDays(settings.date, direction);
    if (settings.live) applyCurrentZonedTime({updateDate: false});
    settings.live = false;
    settings.followToday = false;
    await fetchPanchang(direction, 'push');
  }

  async function refreshNow({manual = false, preserveScroll = true} = {}) {
    if (loading) return false;
    const timelineState = preserveScroll ? captureTimelineState() : null;
    if (settings.live) {
      settings.followToday = true;
      applyCurrentZonedTime({updateDate: true});
    }
    const ok = await fetchPanchang(0, 'replace', {timelineState, showMask: manual});
    if (ok && manual) showToast(state.ui.refreshed);
    return ok;
  }

  dayRail.addEventListener('scroll', () => {
    if (suppressDayScroll || loading) return;
    window.clearTimeout(dayScrollTimer);
    dayScrollTimer = window.setTimeout(() => {
      const width = Math.max(1, dayRail.clientWidth);
      const page = Math.round(dayRail.scrollLeft / width);
      const distance = Math.abs(dayRail.scrollLeft - page * width);
      if (distance > width * .24) return;
      if (page === 0) shiftDay(-1);
      if (page === 2) shiftDay(1);
    }, 150);
  }, {passive: true});

  dayRail.addEventListener('wheel', event => {
    if (!event.deltaX && !event.deltaY) return;
    event.preventDefault();
    dayRail.scrollLeft += Math.abs(event.deltaX) > Math.abs(event.deltaY) ? event.deltaX : event.deltaY;
  }, {passive: false});

  previousDayButton.addEventListener('click', () => shiftDay(-1));
  nextDayButton.addEventListener('click', () => shiftDay(1));

  function openDialog() {
    syncForm();
    if (typeof dialog.showModal === 'function') dialog.showModal();
    else dialog.setAttribute('open', '');
    requestAnimationFrame(() => placeInput.focus());
  }

  function closeDialog() {
    if (typeof dialog.close === 'function' && dialog.open) dialog.close();
    else dialog.removeAttribute('open');
  }

  function syncForm() {
    placeInput.value = settings.place;
    dateInput.value = settings.date;
    timeInput.value = settings.time;
    languageInput.value = settings.language;
    liveInput.checked = Boolean(settings.live);
    syncDateDisplay();
    updateThemeToggle();
    toggleLiveFields({syncNow: false});
    placeResults.innerHTML = '';
    selectedPlace = true;
    updateOgPreview();
  }

  function toggleLiveFields({syncNow = true} = {}) {
    settings.live = Boolean(liveInput.checked);
    liveInput.setAttribute('aria-checked', String(settings.live));
    // Date and Time stay editable in both modes. Changing either field below
    // automatically switches to manual mode, so a user's selection is never
    // silently ignored while the live switch is on.
    dateInput.disabled = false;
    timeInput.disabled = false;
    dateInput.setAttribute('aria-disabled', 'false');
    timeInput.setAttribute('aria-disabled', 'false');
    if (settings.live) {
      settings.followToday = true;
      if (syncNow) applyCurrentZonedTime({updateDate: true});
      dateInput.value = settings.date;
      timeInput.value = settings.time;
      lastLiveMinute = '';
    } else {
      settings.followToday = false;
      settings.date = dateInput.value || settings.date;
      settings.time = timeInput.value || settings.time;
    }
    syncDateDisplay();
    liveIndicator.hidden = !settings.live;
    updateOgPreview();
  }

  function adoptManualDateTime() {
    if (liveInput.checked) {
      liveInput.checked = false;
      settings.live = false;
      settings.followToday = false;
      liveInput.setAttribute('aria-checked', 'false');
      liveIndicator.hidden = true;
    }
    settings.date = dateInput.value || settings.date;
    settings.time = timeInput.value || settings.time;
    syncDateDisplay();
    updateOgPreview();
  }

  editButton.addEventListener('click', openDialog);
  closeButton.addEventListener('click', closeDialog);
  cancelButton.addEventListener('click', closeDialog);
  languageInput.addEventListener('change', () => { settings.language = languageInput.value; syncDateDisplay(); updateOgPreview(); });
  dateInput.addEventListener('input', adoptManualDateTime);
  dateInput.addEventListener('change', adoptManualDateTime);
  timeInput.addEventListener('input', adoptManualDateTime);
  timeInput.addEventListener('change', adoptManualDateTime);
  liveInput.addEventListener('change', () => toggleLiveFields({syncNow: true}));
  dialog.addEventListener('click', event => {
    if (event.target === dialog) closeDialog();
  });

  async function searchPlaces(force = false) {
    const query = placeInput.value.trim();
    if (query.length < 2) {
      placeResults.innerHTML = '';
      placeMatches = [];
      return [];
    }
    placeResults.innerHTML = `<p class="sheet-note">${escapeHtml(state.ui.searching)}</p>`;
    try {
      const params = new URLSearchParams({q: query, lang: settings.language});
      const response = await fetch(`/api/places?${params.toString()}`, {headers: {'Accept': 'application/json'}});
      if (!response.ok) throw new Error('Place search failed');
      const payload = await response.json();
      placeMatches = payload.results || [];
      if (!placeMatches.length) {
        placeResults.innerHTML = `<p class="sheet-note">${escapeHtml(state.ui.no_results)}</p>`;
        return [];
      }
      placeResults.innerHTML = placeMatches.map((place, index) => `
        <button class="place-result" type="button" data-place-index="${index}">
          <span class="place-main">${escapeHtml(place.display_name)}</span>
          <span class="place-sub">${escapeHtml(place.timezone)}</span>
        </button>`).join('');
      if (force) choosePlace(placeMatches[0]);
      return placeMatches;
    } catch (error) {
      console.error(error);
      placeMatches = [];
      placeResults.innerHTML = `<p class="sheet-note">${escapeHtml(state.ui.load_error)}</p>`;
      return [];
    }
  }

  function choosePlace(place) {
    settings.place = place.name;
    settings.lat = Number(place.latitude);
    settings.lon = Number(place.longitude);
    settings.timezone = place.timezone || settings.timezone;
    settings.country = place.country || '';
    settings.slug = place.slug || '';
    settings.locationMode = 'manual';
    placeInput.value = place.display_name || place.name;
    selectedPlace = true;
    placeResults.innerHTML = '';
    updateOgPreview();
  }

  placeInput.addEventListener('focus', () => {
    selectWholePlaceOnPointer = true;
    requestAnimationFrame(() => placeInput.select());
  });

  placeInput.addEventListener('pointerup', event => {
    if (!selectWholePlaceOnPointer) return;
    event.preventDefault();
    placeInput.select();
    selectWholePlaceOnPointer = false;
  });

  placeInput.addEventListener('input', () => {
    selectWholePlaceOnPointer = false;
    selectedPlace = placeInput.value.trim() === settings.place;
    window.clearTimeout(searchTimer);
    searchTimer = window.setTimeout(() => searchPlaces(false), 260);
  });

  placeResults.addEventListener('click', event => {
    const button = event.target.closest('[data-place-index]');
    if (!button) return;
    const match = placeMatches[Number(button.dataset.placeIndex)];
    if (match) choosePlace(match);
  });

  function getZonedParts(timezone) {
    const parts = new Intl.DateTimeFormat('en-CA', {
      timeZone: timezone, year: 'numeric', month: '2-digit', day: '2-digit',
      hour: '2-digit', minute: '2-digit', hourCycle: 'h23'
    }).formatToParts(new Date());
    const values = Object.fromEntries(parts.filter(p => p.type !== 'literal').map(p => [p.type, p.value]));
    return {
      year: Number(values.year), month: Number(values.month), day: Number(values.day),
      hour: Number(values.hour), minute: Number(values.minute)
    };
  }

  function applyCurrentZonedTime({updateDate = true} = {}) {
    const parts = getZonedParts(settings.timezone);
    if (updateDate) {
      settings.date = `${parts.year}-${String(parts.month).padStart(2, '0')}-${String(parts.day).padStart(2, '0')}`;
    }
    settings.time = `${String(parts.hour).padStart(2, '0')}:${String(parts.minute).padStart(2, '0')}`;
  }

  async function reverseDetectedLocation(latitude, longitude) {
    try {
      const params = new URLSearchParams({
        lat: String(latitude), lon: String(longitude), lang: settings.language
      });
      const response = await fetch(`/api/reverse-geocode?${params.toString()}`, {
        headers: {'Accept': 'application/json'}, cache: 'no-store'
      });
      if (!response.ok) throw new Error(`HTTP ${response.status}`);
      return await response.json();
    } catch (error) {
      console.warn('Reverse geocoding was unavailable', error);
      return null;
    }
  }

  async function useDeviceLocation({auto = false, fetchImmediately = false} = {}) {
    if (!navigator.geolocation) {
      if (!auto) showToast(state.ui.location_denied);
      return false;
    }
    if (!auto) locationButton.disabled = true;
    try {
      const position = await new Promise((resolve, reject) => navigator.geolocation.getCurrentPosition(resolve, reject, {
        enableHighAccuracy: false, timeout: 9000, maximumAge: 600000
      }));
      settings.lat = Number(position.coords.latitude.toFixed(6));
      settings.lon = Number(position.coords.longitude.toFixed(6));
      settings.timezone = Intl.DateTimeFormat().resolvedOptions().timeZone || settings.timezone;
      const detected = await reverseDetectedLocation(settings.lat, settings.lon);
      settings.place = detected?.name || detected?.city || `${settings.lat.toFixed(2)}, ${settings.lon.toFixed(2)}`;
      settings.country = detected?.country || '';
      settings.slug = detected?.slug || '';
      settings.locationMode = 'auto';
      selectedPlace = true;
      if (settings.live) {
        settings.followToday = true;
        applyCurrentZonedTime();
      }
      placeInput.value = settings.place;
      liveInput.checked = settings.live;
      toggleLiveFields({syncNow: false});
      updateOgPreview();
      if (!auto) showToast(state.ui.location_ready);
      if (fetchImmediately) await fetchPanchang(0, 'replace');
      return true;
    } catch (error) {
      if (!auto) showToast(state.ui.location_denied);
      return false;
    } finally {
      locationButton.disabled = false;
    }
  }

  locationButton.addEventListener('click', () => useDeviceLocation({auto: false, fetchImmediately: false}));

  form.addEventListener('submit', async event => {
    event.preventDefault();
    if (!selectedPlace) {
      const matches = await searchPlaces(true);
      if (!matches.length) {
        showToast(state.ui.place_required);
        placeInput.focus();
        return;
      }
    }
    settings.language = languageInput.value;
    settings.live = Boolean(liveInput.checked);
    if (settings.live) {
      settings.followToday = true;
      applyCurrentZonedTime({updateDate: true});
    } else {
      settings.date = dateInput.value || settings.date;
      settings.time = timeInput.value || settings.time;
      settings.followToday = false;
    }
    if (selectedPlace && settings.locationMode !== 'auto') settings.locationMode = 'manual';
    closeDialog();
    await fetchPanchang(0, 'push');
  });

  function savePreferences() {
    try {
      localStorage.setItem('panchang-preferences-v2', JSON.stringify({
        place: settings.place, lat: settings.lat, lon: settings.lon, timezone: settings.timezone,
        country: settings.country, language: settings.language, slug: settings.slug || '', theme: settings.theme,
        locationMode: settings.locationMode || 'manual'
      }));
    } catch (_) { /* Storage is optional. */ }
  }

  function loadPreferences() {
    try {
      const raw = localStorage.getItem('panchang-preferences-v2');
      return raw ? JSON.parse(raw) : null;
    } catch (_) {
      return null;
    }
  }

  function hasExplicitLocation() {
    const params = new URLSearchParams(location.search);
    return params.has('lat') || params.has('place') || /^\/[a-z]{2}\/panchang\//.test(location.pathname);
  }

  function localizedHeaders(offset = 0) {
    const parts = getZonedParts(settings.timezone);
    const [selectedYear, selectedMonth, selectedDay] = settings.date.split('-').map(Number);
    const dateValue = new Date(Date.UTC(selectedYear, selectedMonth - 1, selectedDay + offset, 12));
    const months = Array.isArray(state.months) && state.months.length === 12
      ? state.months
      : ['Jan', 'Feb', 'Mar', 'Apr', 'May', 'Jun', 'Jul', 'Aug', 'Sept', 'Oct', 'Nov', 'Dec'];
    const dateText = `${dateValue.getUTCDate()} ${months[dateValue.getUTCMonth()]} ${dateValue.getUTCFullYear()}`;
    const displayHour = parts.hour % 12 || 12;
    const timeText = `${displayHour}:${String(parts.minute).padStart(2, '0')} ${parts.hour < 12 ? 'AM' : 'PM'}`;
    return {
      full: `${state.ui.panchang} (${settings.place} - ${dateText} - ${timeText})`,
      compact: `${settings.place} · ${dateText} · ${timeText}`
    };
  }

  function liveTick() {
    if (!settings.live || loading) return;
    const parts = getZonedParts(settings.timezone);
    const minuteKey = `${parts.year}-${parts.month}-${parts.day}-${parts.hour}-${parts.minute}`;
    if (minuteKey === lastLiveMinute) return;
    lastLiveMinute = minuteKey;
    applyCurrentZonedTime({updateDate: settings.followToday});
    const previous = localizedHeaders(-1);
    const current = localizedHeaders(0);
    const next = localizedHeaders(1);
    state.headers = {previous: previous.full, current: current.full, next: next.full};
    state.headers_compact = {previous: previous.compact, current: current.compact, next: next.compact};
    const panels = $$('.day-panel .day-title', dayRail);
    const values = [previous, current, next];
    panels.forEach((panel, index) => {
      const fullNode = $('.header-full', panel);
      const compactNode = $('.header-compact', panel);
      if (fullNode) fullNode.textContent = values[index].full;
      if (compactNode) compactNode.textContent = values[index].compact;
    });
    if (dialog.open && liveInput.checked) {
      dateInput.value = settings.date;
      timeInput.value = settings.time;
      syncDateDisplay();
      updateOgPreview();
    }
    fitHeaderText();
  }

  function currentZonedMinuteKey() {
    const parts = getZonedParts(settings.timezone);
    return `${parts.year}-${String(parts.month).padStart(2, '0')}-${String(parts.day).padStart(2, '0')}T${String(parts.hour).padStart(2, '0')}:${String(parts.minute).padStart(2, '0')}`;
  }

  async function minuteRefresh({force = false} = {}) {
    if (!settings.live || document.visibilityState !== 'visible') return false;
    if (loading) {
      window.clearTimeout(minuteRefreshRetryTimer);
      minuteRefreshRetryTimer = window.setTimeout(() => minuteRefresh({force: true}), 1200);
      return false;
    }
    const minuteKey = currentZonedMinuteKey();
    if (!force && minuteKey === lastDataMinute) return true;
    settings.followToday = true;
    applyCurrentZonedTime({updateDate: true});
    if (dialog.open && liveInput.checked) {
      dateInput.value = settings.date;
      timeInput.value = settings.time;
      syncDateDisplay();
      updateOgPreview();
    }
    return refreshNow({manual: false, preserveScroll: true});
  }

  function scheduleMinuteRefresh() {
    window.clearTimeout(minuteRefreshTimer);
    const delay = 60000 - (Date.now() % 60000) + 350;
    minuteRefreshTimer = window.setTimeout(async () => {
      await minuteRefresh({force: true});
      scheduleMinuteRefresh();
    }, delay);
  }

  window.addEventListener('resize', () => {
    fitHeaderText();
    centerCurrentItems();
    suppressDayScroll = true;
    centerDayRail();
    window.setTimeout(() => { suppressDayScroll = false; }, 80);
  }, {passive: true});

  window.addEventListener('popstate', () => location.reload());
  window.addEventListener('keydown', event => {
    if (event.altKey && event.key === 'ArrowLeft') { event.preventDefault(); shiftDay(-1); }
    if (event.altKey && event.key === 'ArrowRight') { event.preventDefault(); shiftDay(1); }
    if (!event.altKey && !event.ctrlKey && !event.metaKey && event.key.toLowerCase() === 'e' && !dialog.open) openDialog();
    if (event.key === 'Escape' && dialog.open) closeDialog();
  });

  function applyUjjainFallback(language = settings.language) {
    const fallback = state.default_location || {
      name: 'Ujjain', lat: 23.1765, lon: 75.7885, timezone: 'Asia/Kolkata', country: 'India', slug: 'ujjain'
    };
    settings = {
      ...settings, place: fallback.name, slug: fallback.slug || 'ujjain', lat: Number(fallback.lat), lon: Number(fallback.lon),
      timezone: fallback.timezone, country: fallback.country || 'India', language, live: true, followToday: true, locationMode: 'default'
    };
    applyCurrentZonedTime();
  }

  async function mayRequestGeolocation() {
    if (!navigator.geolocation) return false;
    try {
      if (navigator.permissions?.query) {
        const permission = await navigator.permissions.query({name: 'geolocation'});
        if (permission.state === 'denied') return false;
        if (permission.state === 'granted') return true;
      }
    } catch (_) { /* Some browsers do not expose geolocation permission state. */ }
    try {
      if (sessionStorage.getItem('panchang-location-requested')) return false;
      sessionStorage.setItem('panchang-location-requested', '1');
    } catch (_) { /* Session storage is optional. */ }
    return true;
  }

  async function personalizeInitialView() {
    if (hasExplicitLocation()) return;
    const saved = loadPreferences();
    const savedLanguage = saved?.language || settings.language;

    if (saved?.locationMode === 'manual' && Number.isFinite(Number(saved.lat)) && Number.isFinite(Number(saved.lon))) {
      settings = {...settings, ...saved, language: savedLanguage, live: true, followToday: true, locationMode: 'manual'};
      applyCurrentZonedTime();
      await fetchPanchang(0, 'replace', {showMask: false});
      return;
    }

    if (await mayRequestGeolocation()) {
      const located = await useDeviceLocation({auto: true, fetchImmediately: true});
      if (located) return;
    }

    if (saved?.locationMode === 'auto' && Number.isFinite(Number(saved.lat)) && Number.isFinite(Number(saved.lon))) {
      settings = {...settings, ...saved, language: savedLanguage, live: true, followToday: true, locationMode: 'auto'};
      applyCurrentZonedTime();
      await fetchPanchang(0, 'replace', {showMask: false});
      return;
    }

    const alreadyUjjain = settings.place === (state.default_location?.name || 'Ujjain')
      && Math.abs(Number(settings.lat) - Number(state.default_location?.lat || 23.1765)) < .001
      && settings.language === savedLanguage;
    applyUjjainFallback(savedLanguage);
    if (!alreadyUjjain) await fetchPanchang(0, 'replace', {showMask: false});
  }

  if ('serviceWorker' in navigator && (location.protocol === 'https:' || ['localhost', '127.0.0.1'].includes(location.hostname))) {
    window.addEventListener('load', () => ensureServiceWorker().catch(() => undefined));
  }

  document.addEventListener('visibilitychange', () => {
    if (document.visibilityState !== 'visible') return;
    scheduleMinuteRefresh();
    if (settings.live && (Date.now() - lastDataFetch >= 55000 || currentZonedMinuteKey() !== lastDataMinute)) {
      minuteRefresh({force: true});
    }
    if (shouldOfferDailyPanchang && !dailyPrompt?.open) scheduleDailyPrompt(900);
  });

  // A browser may restore the page from its back-forward cache without a new
  // HTTP request. Recalculate immediately so every visible reload/resume uses
  // the current local date and minute rather than a stale snapshot.
  window.addEventListener('pageshow', event => {
    scheduleMinuteRefresh();
    if (settings.live && (event.persisted || Date.now() - lastDataFetch >= 55000 || currentZonedMinuteKey() !== lastDataMinute)) {
      minuteRefresh({force: true});
    }
  });

  renderAll();
  window.setInterval(liveTick, 15000);
  liveTick();
  scheduleMinuteRefresh();
  Promise.resolve(personalizeInitialView()).finally(async () => {
    await syncDailyPushSubscription({force: true});
    if (shouldOfferDailyPanchang) scheduleDailyPrompt(1800);
  });
})();
"""

# ---------------------------------------------------------------------------
# Embedded raster assets (keeps deployment to panchang.py + requirements.txt)
# ---------------------------------------------------------------------------

ICON_192_B64 = (
    "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"
)

ICON_512_B64 = (
    "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"
)

FAVICON_B64 = (
    "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"
    "AAAASUVORK5CYII="
)

BADGE_96_B64 = (
    "iVBORw0KGgoAAAANSUhEUgAAAGAAAABgCAYAAADimHc4AAACV0lEQVR42u2cUZIDIQhEo7X3v7L7k49UqrI1s6GhxdcXEHgiMDE+HgghhBAq0djR6LXW+ujQGFv5NNmDAAAAAgAAEAAAgAAAALQxgL8m1E6K9HNGG9UdQrSfU7EjukJQ+DmU6bjbh7EKP6fKqE6ZoPTzKwBXyO8O4Yr9ZRnQHYI6+GFFuCOEjOCHFOFso7usIQGg6BZCWr3gdSO7u5GVvneNVhxZETZEt9ayPv3V+DtGZ9SK/9qjmGukg9Jaa101uqJI37FNNVRaTKqVHVL1tD5PDr7D+vNk5y0ycDenlUNfxXE0dgl+1gyRDWG4Bz8iIBVrWgK4EwhFEKrXt+yCMp13/IFouO3+b4ps9NCXAWyesPOdM2G67P707sPkNwwuZnXPAMfd75QFZMAJNcC5IB7/NZQMKDz/o3ef6iOcsg78RC2YlcpXbqm52HIlTlsdQVcd3ukOEjUAAABoqfUUADapGwAQdlrO2TAqd983AY2GmD2zpABwhfC+blXwPw5iOx9Hzl9fLWtA9NnscAv7+C5oPOW++1MAVP7oEfGRTQ2s/Rzwmg1cSzEqji72WGVAVkF0Gspm5lHgEBynS1m2NUAFwfFzBLeji2sR/w8onhP4h0zxkFbaFzudyVUzwjzRaSc7uBnX+WacW8/tOJvwVoTIj1IAvJZSCID3ggoB8GJWIYDdfot18WcS/PyJOxRAx+BnQpgEvxaC9OXcLm9HK/0MCVBGv1zRImb4KXk5t9Or6Wo/Z7RxXYOv8nMqd0h3CHYAEAAAgAAAAAQAACAAAAAhhBBCn/ULQlDsrFpJMjEAAAAASUVORK5CYII="
)


OG_IMAGE_B64 = (
    "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"
    "0oLw869/2vHTnxKJROMEimTn5K1/6pXmZukuIpHI1cXJzdVZJJLWQ0NDw6MbXqiuqemwky0pKYu+G8v+Ce/t7DDmz5nGLs+bMxUP"
    "Hui13LgZ/fL/PmB/Wlpa7PzpMwsLc4G7r37kAWZBrKe38qHFPfO1ZGIcFhIcFhLcr28fKysL7qYT/134a/fB3nz/HDh8kn/9oZN4"
    "uIAyLCzMLSzMLczNuG0VQkhzs+TxZ7ZUVlXjfHstaJ71cpguQS2lYEuzpGueIU3T7PLCeTP27j+qbgJFdu89XFFZxf4cN2b4x++/"
    "6uLsSAjJzSvY/Mq7p89eZjZlZOYcO3Fu0fwZPeN2SY65qGyTvoG+kBzeef35QQNCY+8nBPbx41ofAHoVuXkFax7f3NjYyIq6HV+/"
    "7+PlITyHlzc/MWXSmLT0zP7h/dTasRsR1MePO+TywOGTTz33WmNTE/Pz0NH/li2Z0zvvn/r6huMnz7E/AwN84xKSmeWbkXcys3Lc"
    "3VzwlAFF4qNb3IwbGxsjbkS9+Op7KakZzJrsnLzDR0/3sGeqt52vNqB51jsxMRYRQmswULD7CUIGL0+3be++MmLYIGV6r80EXGLv"
    "J3J/frrtNSdHe2bZ2clhx9cf9B8+o7y8gn099xhBaGJirGUOIpFowdxpC+bC1oDeS319w6p1zxcWlUjfxG9sHj1yCDcNN1TJW69t"
    "CvDz3vrh1/EJyYaGhkwTR0Usk7Pnr+z869/U1IzMrFxDQwMPd5e+QQHr1iwP8PdRVqTmZslPv+3a9c+hlLQMB3vbsJDglzc/4eXp"
    "pliYpx5f+eKmDUzi1PRMezsbucQsZWUVP/7696UrN7OycwuLih3s7dxcncaNGb7q4SXmZqYa1NvcWVMibkSxTrb3YuJ0ciyJRLJq"
    "3fMnT19g13zzxdZ5s6e0R03qqnLOnLtcVS31PXntlWdWrH6W9XM5eOS/Jx57WNnttO3dV5Yunv3Vt7/u2Xc0Jy/fxclx0YIZT65/"
    "RF9fv6Gh4dsf/th34FhGZo6zo8OQweEvb37Cwd5W3cJzDzdsyIB/d33P3X3QyFnZOXnM8oNL53/03hZ1K6TN6zJn0eobt+4wy0MH"
    "99+/ewd39wHDZ+TmFTDLDy1fsO3dV9rjdu3i6Ovrjxox+Nsvtk6ZvYJdeSvyTk8VSL3tfNE8A4LVoO7pooJQT0/vyfWPbHpmnZGR"
    "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"
    "NDDQf/bJR7usVyRFUcuXzP3x113sK3n63IeHDRlASyTXbtxWnHaC/ZrLcPT42YeWzdfX19938Pgvv+9RdpTJk8bYWFsxup07hRfC"
    "yYBOJDjQ//F1D33Z+vovLCr531sfffnJW5rlZmdrs3jBTPZj01+7D7LxdbkqSK5Pvh1Oys/AwIAdGrRkxQZ7O5uKyqr6+gaRSKRD"
    "faKTY82bPeXfA8dPnm4Jdbh3/9G5sydPnjC6nWpSmwIXFpVcuXaL/enl6fbpttcUk92OjmEjZuXlF16/GTVsyIDOqu0xo4eyhpdl"
    "yKBwtmmrVp4a3OEO9rZjRw87c+4KN82sGZOMjAw7/nbtLvh4y/gcffrlD9/+8LtYT0/7iDuLFsxgJ9njzgM8f840prNLs/d7B6OT"
    "Qj6yYtHX3/3W+lWiYsrsFZMmjJI0N585d0XZyNX2uy4A6JZe5JG8cN507lAT0hpmKjEpVU4NhvQLfOKxR5jlKRPHcJ0h/z144vGn"
    "X3l285tcNfjYow/yThRhZmpCUVRySvqRY2e4apAQ8txTj7JhrOT2jYlN+GL7zx999n1zc1NXrs/nn32MiZzOUFdXf+7C1fOXIurr"
    "G7jrGQL8fLif1t55/4ug/hN9+45+/qV3iHLPe32xmPVIYTEwwPSDoJPZ+PRabmjKPf8e5c4coy4fvf/qnJlKb+nw0OCfv/uovc/I"
    "wMDgrf9tlFMy9fUNw4cOGDakfxc81gfvvGTOCar5witbKyoq26kmtSnwoaP/cfUJ18dMRu1Mn8j9uf/QyU6sbbGe3uyZk+RWsl7T"
    "GuSpwXVZvEB+UMAizrugI2/X7sKCudPlwoTW1tYxqsPZyUErqenlMSC8H69Q1Ob93sHopJBPP7GaG32noqJy3/5j+w+drKisUhab"
    "vf2uCwAQhBpCUdR3X259cdPjKiav09fXf2j5gj1/fMN+iSSEfPbhG089vpK3s05fLH56w6o3tjzHm5uvj9ejK5cqFuOZJ1Y/smIR"
    "u8bP12sxJ5R2d8HKyuL3nz5zcXZUXM9GdmbR0xNt27qFu0YikdA0bWVlsWH9wyqOsmzJHLk10yaPVRScAHQkRkaGH8g6BWzeslXj"
    "2IZiPb3vvnrv2IHfFs2f0Tc4wMLC3MjI0N/Pe+qkMb/+8MnR/b92zHybj6xY9NevX44dPczJycHAwMDTw/XJ9Y/8+cuXckE4u8ix"
    "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"
    "NzR+seOfe/dTPv9+d3pmnurENE2+/nHvpWvRg8KD5s8Y29TU/Ok3fyenZbMPTEZ2fovC/HX/7v2n+/h5cHcvLC774Iudzc2SpQsm"
    "Txk35E5s0pc7dksktPLD0Tdux3q6OUVExtAKqUQi0b245IrKarn1V2/cFYk6ruYF1glDakbuh1/9UVtXP2vKyIljBmXlFHz41R/V"
    "NXWKpuePvSdUn4WpqfGG1Qs3rF64cunMIH+vI/9d+fH3Q12wfgDg+QLFZx+amps/2v7n3dik8aMGTJ84LDkte9uXO2vr6hVzKCgs"
    "ff/z3/ILSqZNHLZo9ng7G8ud/xzbd/ic9mU7fOry2x//rKsycx9/HT77nWseFatCWeV07iVjDvrhV3/UNzQuWzBlwaxxOflFH331"
    "Z3V1La9xLimtIISsfnA2Y1c3rF74+Kr5hBBnRzt2DfM3buQAQoi5uUm3fnPB/nQj+9Nm80nuZhZ4LgKtjerGRjvdz7yXqRNNjYpL"
    "w1sq7hVRVmzVrceucBVALxKEjY1NX/2wRyzWc7C3Hjow+NNv/+baFEXuJ6TGxKdufnLFzMkjxo8asGnDcjtbqxNnrrV8w9h78p2P"
    "f05KzUrPyktNz9n85IPDBvbj7n76wg1TU+On1y4ZNrDvhNGD1j8yPyU9JzElQ9nhEpIzyiurly+aWlxSnpyWJbfVzcXB0MDg2s17"
    "3JV19Q2RdxNUdNDpHIF1wvw8c/Gmg7315icfnDB60PSJw597fGlZeWXUvQS5PA+euERoMmxgXxXHNdAXh/fzD+/nP2RA8OK5E5bM"
    "nXgrOi6voKSr1Q8AciizDzej4jKz85957IHJ44aMHzVw4+PLSsoqL0VEK+Zw+uINIyODF55aMW7kgLEj+q9fOX/6xOH/XbhRX9/Q"
    "pcrMffx1+Ox3rnlUrAplldO5l4wQcvXWPZFI9My6JUMGBI8YHPLMuiUlZRVRMYm8xrm4tFxfLB42sC9jV8P7+Yf19SeEmJoYsWuY"
    "v9T0nEB/Tw9Xx2795oL96Ub2p83mk9zNLPBcBFob1Y2NdrqfeS9T1zQ1vKXiXhFlxVbdeuwKVwHokC7tMtrY1PTVj3vKK6peeuah"
    "F9/aHhrsLxKJPv32702PL3NzceDd5fyV2/1DApwdbVtOT6z31ktr2a0DQgPq6xucHe0aGhpf3bTKzNS4oKiUu7unu7OXh4tY3OLW"
    "6OhgQwgpKinvo6SEEZGxPp4u3h7O7q6OEbdi/LzdZL+zUmF9/S5fvztl/FB25a2ouObm5r6B3vFJ6R1TjQLrhPm5atksiiKs64Kp"
    "sRFFUfX1jdwMM7Pz/zt/44nVC+/FpQgvBvPlKS+/yMnBpkvVDwBy2Nta89qHK9fvBPp5ujrbMz9tbSzD+vpdjrgzeewQuRwKi8vs"
    "bKwMOA4w0yeNGDYoRK/VZTo1I/ffI+czsvJMjI0G9Q+cNXkkm3jbl7+7Otv7ersdOn6xuqbOy8N5ydyJLk52hJDX3t+RV1BMCFm3"
    "8f2BYYGPPTJPyzJzH3+dP/udZR4Vq0JZ5XTuJWOaUAYG+vr6LS9iUxNjkYhqaGjiNc4lpRXW1uZtnv7d+8npWXmbNizvgpcG9FT7"
    "02bzSe5mFnIumrU0FBsb7XQ/816mdjU1Gl8a3lJxr4iyYqtuPXaFqwB0SNftIWxqat7+076cvKKn1i42MTZqbGxqbGpaPGdigI/7"
    "p9/+nZNXxLtXdl6hp5vTpWvRWz/79dktn33yzd+ZnB7FsL7+61fONzUxsrYy5/VWHz6oH/db1J3YZEKIp5sTfwmbmyOj4weFBxFC"
    "BocH3YyOa26WcBNIJPTg/sG5+UVpGblSm37jbr9AHyNDgw6rSYF1wjYF2BZhcWn5r7uOWpqbDgyTKmKapnf+c3xAaEBIsK9axSgq"
    "KSeEWFqad7X6AT0CWod5KbMPBYWlPl6u3DW+Xq68L34/b/ek1MzzV243NTczawwN9J0cbJjWUnJa9odf/m5hbrJy6YxJYwdfvBb9"
    "819HuLsnpmQePXVl+sThS+dPqq2te++zX4tLygkh61fOHz44xNLCbMvGlQtmjdO+zNzHX7fPfieaR8WqUFY5nXvJCCGDwoMaGxv/"
    "PXK+prauorL69z0nrCzM2TqXM84lpRUiitr+095nXvl0y7vf7j18rqmpWfFEjpy64uftpsJjrbu8uWB/upH9abP5JHczt3kuGrc0"
    "FBsb7XQ/816m9jY1ml0a3lJxr4iyYqtuPXaFqwB0SNftISwuLS8prdi0YRk3qoFIRK19eO63P/8bn5TBfBeRo7Ss8lZ0XGVVzZTx"
    "QwwM9M9dinzv899ee361k4OtugUor6jad/jcgNA+ynoj791Pqa2rHxQeSAgZMiD436Pn7sWlhPX141q0voHe5mYml6/f8fJwZr4M"
    "JaVmrn1oXmVVjbLjnjp//fSFm5s2LOcN50DThHfgsbL1mtVJVk7BWx/9xHy3e+mZhy0tzNhNZy/dKigsfXLNIuE12djUlJ6Z98+B"
    "M86OdlwvJs3qB4DOafHRdFlFldxYfHNz06am5qrqWrm36ZRxQzKz8//Yc+Lg8Yv9QwLC+wUE9/FiR0rsPXQ2rJ//oyvmMD8d7Ky/"
    "2LE7PTPP072l8ZRfWPLulvU2VhaEkAGhfV5599vDpy4/8sAMFyc7SwtTsVhP2Vcqbcqs22e/Pczj3dhk3vUaNBkV6ZRLZm9r9cSa"
    "RZ99t+vY6auEEDNT4xeeWsEb74EQoqcnqm9odHKwHRAWmJGVd+rc9bz8oidkL8f9hLSUtOxn1j3QwZcGwP4Ibz4JORcNWhrKGhs9"
    "ydTo6tUgEM1a1Lq6CgCCsAVHe5s3XlijGHZJrKf3xJqFvOGYmpqaGxub8gtL3nxxrbWVOSFkSP/g1z/44cCxi3Id6ELMyjc/79PT"
    "E61YPE1ZmuuRMX38PJkGk421RYCv5/VbMdzXKiFEJBINHxxy6Vr0knkT9cXiqzfumhgbhffzv3gtWlm2lVU1lVU1DQ2NPB8Ii0q/"
    "/eXfxx6Z52hvw13f3Cz57rf9/QJ9xgwP10md2NlYPrFmUVl55aWI6Hc++fm59UvdXR0Z67D/6IVFcyYoa7LImZJ1G99nf3q6O61e"
    "PltPT6Rl/QDQBdtq8mZKrPfYI/NS0nOu3bx3JzbpwtUoJwebNSvmeLo5NTY1JadlL5o9PiungElsYW4iFutlZEsbZH7e7swrnxBi"
    "YKA/MKxPXGJ6e5dZh89+O5nHL3/4h3f995+8pIN3YWdcsrjEtC92/NMvyHfYwL5NTc3nLke+//nOzU8+yLrScVn70Fx2edjAvs6O"
    "tjt3H09KzeI6fB4+ddnT3UlFcNH2e3MB2B/hzSfV56KutWmzsdFjTE0HvBo0bj3q/CoACEIpyoLwKlsvFuuJxXohQb7Mvcs8MANC"
    "+9y6E6fWcSUSesfOg3kFJS8+/ZCy3v+6+obomKTGxibuA6CvL66rb5Dr/h41NPTk2Yioe4mDw4Ou3YwZOrAv62TPy4KZ4+ZMHc2b"
    "xtrS3MzU+OPtf7341ApbG0vWgP7w+8HE5IzZU0bqqk6MjAyZ9sHIIaFvffTTv0fPP712CSHkr30n3VwcRg8LF1KNpqbGjzwwgxCi"
    "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"
    "2uiWGikoef2DHTRNGxkavLtlvbmZCe4kAGvYk2yiOi0naZQ/vjaZVuG2EpIzPvr6T0LIpDGDl8ybyKz8ddfRyxF3/t/efYdFcXVx"
    "AD6zu/Tei/ReFFRU7L1i78bYosZUUzSa9qU3oyYxPTExxqgpdo3d2CsiCAqIIL333ln2+2NgGLaxwIKgv/fJY3ZmZ2futMM9M3fu"
    "EFGAv9czS2dglwE8AtkgPydszZWjDow/nNz8orc/+Yn9bGxk8Pm7L6jY+KuwqDQ3v5CI7HtY6WhrVVRWbfn5n6qq6meWzuxhY9H+"
    "gkkkdPlGeNid+2kZORKJxNrKbMgAv0H9erKN07j4OX/G2DHD+6lrH6lrtj/vOBQaEUNEP21+vaq6Wr1bBlD/6ZT6T2MYasi5Wmgj"
    "qmLDUZE6QoPC56rbbPbUUXfvxYvF9f9dDBk9NIDN/Y6evsLOdsLogcgG4dGWVJQb9MfnRGSgpXNl5fsaQuH2sIubrvw7v9eg90bN"
    "JqLEwtzJOz+30jc6v/wdIorMSf362om72akChull5fDq4CAvC9ud4Zc/u3SYnaGBpnZPK/u1Q6aEZiR8dunweDe/LUFLiEgsqd8e"
    "dvHY/dspxXm2BiYzffov9h/2991rcqdJLc53MjGf6d1/of8QhhglRZJbHjVuH8XP8Cjs+q89Ll67zWaDdraWTz0xGccngBpVZeXe"
    "XfcZEQl1dfp8/2H0u19VpGbYzQ2ymTaWneD+Zz+URD+wmTa2x+yJWccvFFwPq8rJ17a2MB/W32rcUGKY7FOXUnYdMhng77Z6KfuZ"
    "rS5pmZnoudjbzZ+iZWnW7eJPaHgM97mouDQ+Kc3N2U6VH94Kv7f3yDkieu2FhR6uDonJmUkpmUQUHZvY/rSnqrrm+2377z9I5saU"
    "llXExafeuBX58qr5QqGgGx146t0ygPpPp9V/SN47b9r55glBm4ui6Cu1hEIrC9MRg/sSUXV1zYmz14koKyc/5PY9IjI21B83oj9O"
    "GHi0nYyLICKGmNLqymupsconzi4rXnHg56spsea6BsbaepeTY1Ye2lpYWc5+a6qj37+Hq4ZQdD017unDWytra/i/XXN855dXj8Xm"
    "ZeqINOMLsjdfOfruub1S8+em0dPUis5J/+TioXfP7m1zedQbE4kYtq8tNkJ2RDaYkJzxz8H/iEhfT+eF5bM1NTVwfAKoUUFwOJu/"
    "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"
    "ZPOowsLizVu2srXDA4dOXLkW0ubt8MTcadznH7b+wd126Nu7p1RbTXXx9HCx4a34H7v3c72cxcTGs9kvy8ba0sPdRfnccnLzuecQ"
    "iGjX9q+fWfmkl4erhkj0ID4JpyU8dE8umGlmasINJqekT5y2+Mtvfrlw6XpsXMLZ81dXr3l3zesfNUVSgeDJBTM69KyXYqCvd+zg"
    "7yN418Ku3Qj9dftfHXSWzZw2gf2gqam58ZO3+F999NnX3JPValko4gPAwzr71FL9UHtJahSoratr1bJsrC35Dfv/+PMAd8suNS3j"
    "O8Xv3FIdwhd0U6LuVVwnR7uevp78J5iJaMqkscp/9f47ry5d2fAO0N/+2FNYVDx+7Ijq6urzF68fPnqam0wqziryzhsvvfDK/9jP"
    "JSWlE6YuHjakPyMQnD1/lbtpKRIKhw8LJCIXZ3v+b7/69tefft0lEgpLy8rbsx3GjR1uamLMPhtdWVnFje+I7mQ4/+OteHlFRdCM"
    "pUMG9WMY5sq1kKqqav5kLc6K31E+ER0/eX7xEzM1NDQOHDn5+659OC3hodPV1fl68/uLV7zC3XMrK6/Y9NXPiqZfvHCWr7dH40Wo"
    "DjnrZS51Obq5On35+TujJsznrkZ/svG7kcMHsdWyjjvLhgzqN3fW5L0HjnFbZt1bn+z67Wt1LRTxAeBhnX1qqX6ovSSOnoPlF2b0"
    "sDfXv9CqZS1dNOf7nxuagxUXl4yfumjs6KH1YvG5C9fU8t4ghC/oprpfj7dSNwm1tbVGjxys/CfjxwyfMXU8N3jwyKnnXnrrlXUf"
    "8LPBZ1Y+6enhokoBZk2fOHHcCG6wvKLi5JmLJ06d57/G8P131rCPes+aPkmqm9DKyiq2Xsi/4dZaGiLRbJl3WmhqdsjrB/krPnnS"
    "aG6wqqr67Pmr/527ws8GgyaOlmprJ5eHmwv/Kt3HG77x7jPG1XfYa2983K7HNAHUZ8yoIZ+8v04gaDlIjhw+6KP3XuOdKR1y1stl"
    "a2P1wTtruMHq6prVa95jr9l36Fn23tuvsO9lZZ09f/XAoRPqWijiA8DDOvvUUv3ozFO4tct66YXl/C7uSkpKDxw6cejf0yWlZVJx"
    "u3PKA4CEsK0J4eSxUpU2Vc7hLZveX/3cMrm9rWiIRC89/9T7b7+qehm+3/Lx0089IbemqKOjvX7NsyuWzmcHra0s3lz3gmxXE7Nn"
    "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"
)


HTML_TEMPLATE = r"""<!doctype html>
<html lang="{{ context.lang }}" dir="ltr" data-theme="light" prefix="og: https://ogp.me/ns#">
<head>
  <meta charset="utf-8">
  <meta name="google-adsense-account" content="ca-pub-4357913188792813">
  <meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">
  <meta name="theme-color" content="#35498f">
  <meta name="color-scheme" content="light">
  <meta name="robots" content="index,follow,max-image-preview:large,max-snippet:-1,max-video-preview:-1">
  <meta name="googlebot" content="index,follow,max-image-preview:large,max-snippet:-1">
  <meta name="author" content="{{ app_name }}">
  <meta name="application-name" content="{{ app_name }}">
  <meta name="apple-mobile-web-app-title" content="{{ app_name }}">
  <meta name="mobile-web-app-capable" content="yes">
  <meta name="apple-mobile-web-app-capable" content="yes">
  <meta name="apple-mobile-web-app-status-bar-style" content="black-translucent">
  <meta name="format-detection" content="telephone=no">
  <meta name="description" content="{{ seo.description }}">
  <meta name="abstract" content="{{ seo["copy"] }}">
  <meta name="keywords" content="{{ seo.keywords }}">
  <script nonce="{{ nonce }}">try{document.documentElement.dataset.theme=localStorage.getItem('panchang-theme')==='dark'?'dark':'light'}catch(e){document.documentElement.dataset.theme='light'}</script>
<!-- Google tag (gtag.js) -->
<script async src="https://www.googletagmanager.com/gtag/js?id=G-QECHKT2KS4"></script>
<script>
  window.dataLayer = window.dataLayer || [];
  function gtag(){dataLayer.push(arguments);}
  gtag('js', new Date());

  gtag('config', 'G-QECHKT2KS4');
</script>
  <title>{{ seo.title }}</title>
  <link rel="canonical" href="{{ seo.canonical }}">
  {% for code, href in seo.alternates.items() %}<link rel="alternate" hreflang="{{ code }}" href="{{ href }}">
  {% endfor %}
  <link rel="alternate" type="application/json" title="Machine-readable Panchang" href="{{ api_href }}">
  <link rel="alternate" type="text/plain" title="AI-readable site guide" href="{{ root }}/llms.txt">
  <link rel="manifest" href="{{ root }}/manifest.webmanifest">
  <link rel="icon" href="{{ root }}/favicon.ico" sizes="any">
  <link rel="icon" type="image/png" href="{{ root }}/icon-192.png" sizes="192x192">
  <link rel="apple-touch-icon" href="{{ root }}/icon-192.png">
  <link rel="image_src" href="{{ seo.og_image }}">

  <meta property="og:type" content="website">
  <meta property="og:site_name" content="{{ app_name }}">
  <meta property="og:locale" content="{{ og_locale }}">
  {% for locale in og_locale_alternates %}<meta property="og:locale:alternate" content="{{ locale }}">
  {% endfor %}
  <meta property="og:title" content="{{ seo.title }}">
  <meta property="og:description" content="{{ seo.description }}">
  <meta property="og:url" content="{{ seo.canonical }}">
  <meta property="og:updated_time" content="{{ data.generated_at }}">
  <meta property="og:image" content="{{ seo.og_image }}">
  <meta property="og:image:url" content="{{ seo.og_image }}">
  <meta property="og:image:secure_url" content="{{ seo.og_image }}">
  <meta property="og:image:type" content="image/png">
  <meta property="og:image:width" content="1200">
  <meta property="og:image:height" content="630">
  <meta property="og:image:alt" content="{{ seo.image_alt }}">
  <meta name="twitter:card" content="summary_large_image">
  <meta name="twitter:title" content="{{ seo.title }}">
  <meta name="twitter:description" content="{{ seo.description }}">
  <meta name="twitter:image" content="{{ seo.og_image }}">
  <meta name="twitter:image:src" content="{{ seo.og_image }}">
  <meta name="twitter:image:alt" content="{{ seo.image_alt }}">
  <meta itemprop="image" content="{{ seo.og_image }}">

  <style nonce="{{ nonce }}">
  {{ css | safe }}
  .sr-only { position:absolute!important; width:1px!important; height:1px!important; padding:0!important; margin:-1px!important; overflow:hidden!important; clip:rect(0,0,0,0)!important; white-space:nowrap!important; border:0!important; }
  .noscript-card { position:fixed; z-index:100; inset:auto 12px 12px; padding:10px 13px; border:1px solid #555; border-radius:12px; color:#fff; background:#1b1c1e; font-size:12px; box-shadow:0 12px 40px rgba(0,0,0,.28); }
  </style>
  <script id="structuredData" type="application/ld+json" nonce="{{ nonce }}">{{ jsonld_json | safe }}</script>
</head>
<body>
  <div class="ambient" aria-hidden="true"></div>

  <main class="app-shell" id="panchangApp">
    <header class="day-carousel" aria-label="{{ data.ui.swipe_hint }}" title="{{ data.ui.swipe_hint }}">
      <button class="header-control previous-control" id="previousDayButton" type="button" aria-label="{{ data.ui.previous_day }}" title="{{ data.ui.previous_day }}">‹</button>
      <div class="day-rail" id="dayRail" tabindex="0">
        <div class="day-panel" data-position="previous" aria-label="{{ data.ui.previous_day }}">
          <span class="day-title"><span class="header-full">{{ data.headers.previous }}</span><span class="header-compact">{{ data.headers_compact.previous }}</span></span>
        </div>
        <div class="day-panel" data-position="current" aria-label="{{ data.ui.selected_day }}">
          <h1 class="day-title" id="currentHeaderText"><span class="header-full">{{ data.headers.current }}</span><span class="header-compact">{{ data.headers_compact.current }}</span></h1>
        </div>
        <div class="day-panel" data-position="next" aria-label="{{ data.ui.next_day }}">
          <span class="day-title"><span class="header-full">{{ data.headers.next }}</span><span class="header-compact">{{ data.headers_compact.next }}</span></span>
        </div>
      </div>
      <div class="header-actions">
        <button class="header-control next-control" id="nextDayButton" type="button" aria-label="{{ data.ui.next_day }}" title="{{ data.ui.next_day }}">›</button>
      </div>
      <span class="live-dot" id="liveIndicator"{% if not context.live %} hidden{% endif %}>{{ data.ui.live }}</span>
    </header>

    <div class="metrics" id="metrics" aria-live="polite" aria-busy="false">
      <div class="data-rows" id="dataRows">
        {% for section in data.sections %}
        <section class="metric-row" data-section="{{ section.key }}" itemscope itemtype="https://schema.org/Observation">
          <div class="metric-label">
            <span class="metric-icon" aria-hidden="true">{{ section.icon }}</span>
            <h2 itemprop="variableMeasured">{{ section.label }}</h2>
          </div>
          <div class="timeline-wrap">
            <div class="timeline" tabindex="0" role="list" aria-label="{{ section.label }} — {{ data.ui.timeline_hint }}">
              {% for item in section["items"] %}
              <article class="moment {{ item.quality }}{% if item.detail and item.detail == data.ui.mixed %} mixed{% endif %}{% if item.current %} is-current{% endif %}{% if item.starts_day %} starts-day{% endif %}" style="--duration-width:{{ item.width_px }}px;--duration-width-mobile:{{ item.mobile_width_px }}px;--duration-width-landscape:{{ item.landscape_width_px }}px" data-duration-minutes="{{ item.duration_minutes }}" data-day-key="{{ item.day_key }}" role="listitem"{% if item.current %} aria-current="true"{% endif %} aria-label="{{ item.title }}. {{ item.time }}{% if item.quality == 'auspicious' %}. {{ data.ui.good }}{% elif item.quality == 'inauspicious' %}. {{ data.ui.avoid }}{% elif item.detail and item.detail == data.ui.mixed %}. {{ item.detail }}{% endif %}">
                <span class="moment-title" itemprop="value">{{ item.title }}</span>
                <span class="moment-meta">
                  {% if item.crosses_day and item.start_display and item.end_display %}
                  <time class="moment-date moment-endpoint"{% if item.start %} datetime="{{ item.start }}"{% endif %}>{{ item.start_display }}</time>
                  <time class="moment-time moment-endpoint moment-endpoint-end"{% if item.end %} datetime="{{ item.end }}"{% endif %}>→ {{ item.end_display }}</time>
                  {% else %}
                  <span class="moment-date">{{ item.date }}</span>
                  <time class="moment-time"{% if item.start %} datetime="{{ item.start }}"{% endif %}>{{ item.clock }}</time>
                  {% endif %}
                </span>
              </article>
              {% endfor %}
            </div>
          </div>
        </section>
        {% endfor %}
      </div>
      <section class="metric-row reserved-row" data-section="reserved" role="presentation">
        <div class="metric-label blank-label" aria-hidden="true"></div>
        <div class="reserved-slot">
          <script async src="https://pagead2.googlesyndication.com/pagead/js/adsbygoogle.js?client=ca-pub-4357913188792813"
               crossorigin="anonymous"></script>
          <ins class="adsbygoogle"
               style="display:block"
               data-ad-format="fluid"
               data-ad-layout-key="-fb+5w+4e-db+86"
               data-ad-client="ca-pub-4357913188792813"
               data-ad-slot="9007484211"></ins>
          <script nonce="{{ nonce }}">
               (adsbygoogle = window.adsbygoogle || []).push({});
          </script>
        </div>
      </section>
    </div>
  </main>

  <button class="fab" id="editButton" type="button" aria-label="{{ data.ui.edit }}" data-tooltip="{{ data.ui.edit }}">
    <svg viewBox="0 0 24 24" aria-hidden="true"><path d="M12 20h9"/><path d="M16.5 3.5a2.12 2.12 0 0 1 3 3L8 18l-4 1 1-4Z"/></svg>
  </button>

  <dialog class="settings-sheet" id="settingsDialog" aria-labelledby="settingsTitle">
    <form class="settings-form" id="settingsForm">
      <div class="sheet-head">
        <h2 id="settingsTitle" data-i18n="settings">{{ data.ui.settings }}</h2>
        <button class="icon-button" id="closeDialog" type="button" aria-label="{{ data.ui.close }}">×</button>
      </div>
      <div class="sheet-body">
        <button class="theme-toggle-button" id="themeToggleButton" type="button" aria-label="{{ data.ui.appearance }}: {{ data.ui.light_theme }}" aria-pressed="false">
          <span class="theme-glyph" aria-hidden="true">☀</span><span>{{ data.ui.light_theme }}</span>
        </button>

        <div class="field">
          <label for="languageInput" data-i18n="language">{{ data.ui.language }}</label>
          <select id="languageInput">
            {% for language in data.languages %}<option value="{{ language.code }}"{% if language.code == context.lang %} selected{% endif %}>{{ language.native }} — {{ language.name }}</option>{% endfor %}
          </select>
        </div>

        <div class="field">
          <label for="placeInput" data-i18n="place">{{ data.ui.place }}</label>
          <div class="input-shell">
            <input id="placeInput" type="search" value="{{ context.place }}" autocomplete="off" enterkeyhint="search" spellcheck="false" data-i18n-placeholder="search_place" placeholder="{{ data.ui.search_place }}" aria-controls="placeResults" aria-autocomplete="list">
          </div>
          <div class="place-results" id="placeResults" role="listbox" aria-live="polite"></div>
        </div>

        <div class="switch-row">
          <label for="liveInput" data-i18n="live_time">{{ data.ui.live_time }}</label>
          <label class="switch" aria-label="{{ data.ui.live_time }}">
            <input id="liveInput" type="checkbox"{% if context.live %} checked{% endif %} aria-checked="{{ 'true' if context.live else 'false' }}">
            <span class="switch-track" aria-hidden="true"></span>
          </label>
        </div>

        <div class="form-grid">
          <div class="field">
            <label for="dateInput" data-i18n="date">{{ data.ui.date }}</label>
            <div class="date-picker-shell">
              <span class="date-display" id="dateDisplay">{{ data.query.date_display }}</span>
              <span class="date-picker-icon" aria-hidden="true">▦</span>
              <input class="date-native-input" id="dateInput" type="date" min="1600-01-01" max="2400-12-31" value="{{ context.date.isoformat() }}" aria-describedby="dateDisplay" aria-disabled="false">
            </div>
          </div>
          <div class="field">
            <label for="timeInput" data-i18n="time">{{ data.ui.time }}</label>
            <input id="timeInput" type="time" step="60" value="{{ context.time.strftime('%H:%M') }}" aria-disabled="false">
          </div>
        </div>

        <button class="location-button" id="locationButton" type="button" data-i18n="use_location">{{ data.ui.use_location }}</button>

        <figure class="share-preview" aria-label="{{ data.ui.share_image_alt }}">
          <div class="share-preview-frame">
            <img id="ogPreviewImage" src="{{ seo.og_image }}" alt="{{ seo.image_alt }}" width="1200" height="630" loading="eager" decoding="async">
          </div>
        </figure>
        <p class="seo-copy" id="seoCopy" lang="{{ context.lang }}">{{ seo["copy"] }}</p>
      </div>
      <div class="sheet-actions">
        <button class="action-button secondary" id="cancelButton" type="button" data-i18n="cancel">{{ data.ui.cancel }}</button>
        <button class="action-button primary" type="submit" data-i18n="apply">{{ data.ui.apply }}</button>
      </div>
    </form>
  </dialog>

  <dialog class="daily-prompt" id="dailyPrompt" aria-labelledby="dailyPromptTitle">
    <div class="daily-prompt-card">
      <button class="daily-prompt-close" id="dailyPromptClose" type="button" aria-label="{{ data.ui.close }}">×</button>
      <span class="daily-prompt-mark" aria-hidden="true">☼</span>
      <h2 id="dailyPromptTitle" data-i18n="daily_prompt">{{ data.ui.daily_prompt }}</h2>
      <button class="daily-prompt-yes" id="dailyPromptYes" type="button" data-i18n="yes" autofocus>{{ data.ui.yes }}</button>
    </div>
  </dialog>

  <div class="toast" id="toast" role="status" aria-live="polite"></div>
  <div class="loading-mask" id="loadingMask" aria-hidden="true"><span class="spinner"></span></div>
  <noscript><div class="noscript-card">The Panchang is fully visible without JavaScript. Enable JavaScript only for swiping, live time, place search and editing.</div></noscript>

  <script id="initial-data" type="application/json" nonce="{{ nonce }}">{{ initial_json | safe }}</script>
  <script nonce="{{ nonce }}">{{ js | safe }}</script>
</body>
</html>
"""

TEMPLATE_ENV = Environment(loader=BaseLoader(), autoescape=True)
PAGE_TEMPLATE = TEMPLATE_ENV.from_string(HTML_TEMPLATE)


# ---------------------------------------------------------------------------
# HTTP helpers and routes
# ---------------------------------------------------------------------------


def build_payload(context: dict[str, Any]) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    data = build_panchang(context)
    seo = seo_payload(context, data)
    jsonld = build_jsonld(context, data, seo)
    data["seo"] = seo
    data["jsonld"] = jsonld
    return data, seo, jsonld


def plain_not_found() -> Response:
    return Response("Not found", status=404, mimetype="text/plain")


def page_response(path_lang: str | None = None, place_slug: str | None = None, date_str: str | None = None) -> Response:
    if path_lang and path_lang not in LANGUAGES:
        return plain_not_found()
    if place_slug and place_slug not in POPULAR_PLACES and not all(
        request.args.get(key) for key in ("place", "lat", "lon", "tz")
    ):
        return plain_not_found()
    if date_str and not re.fullmatch(r"\d{4}-\d{2}-\d{2}", date_str):
        return plain_not_found()

    context = resolve_context(path_lang, place_slug, date_str)
    if date_str and context["date"].isoformat() != date_str:
        return plain_not_found()

    data, seo, jsonld = build_payload(context)
    push_csrf = request.cookies.get(PUSH_CSRF_COOKIE) or secrets.token_urlsafe(24)
    vapid = push_vapid_config()
    data["push"] = {
        "enabled": push_feature_enabled(),
        "public_key": vapid.get("public", "") if push_feature_enabled() else "",
        "csrf": push_csrf,
        "offer_after_days": PUSH_OFFER_AFTER_DAYS,
        "delivery_hour": PUSH_HOUR_LOCAL,
    }
    nonce = secrets.token_urlsafe(18)
    rendered = PAGE_TEMPLATE.render(
        context=context,
        data=data,
        seo=seo,
        nonce=nonce,
        app_name=APP_NAME,
        root=site_root(),
        api_href=api_url(context),
        og_locale={"en": "en_IN", "ne": "ne_NP"}.get(context["lang"], f"{context['lang']}_IN"),
        og_locale_alternates=[
            {"en": "en_IN", "ne": "ne_NP"}.get(code, f"{code}_IN")
            for code in LANGUAGES if code != context["lang"]
        ],
        css=CSS,
        js=JS,
        initial_json=safe_script_json(data),
        jsonld_json=safe_script_json(jsonld),
    )
    response = make_response(rendered)
    response.mimetype = "text/html"
    response.headers["Content-Type"] = "text/html; charset=utf-8"
    response.headers["Content-Language"] = context["lang"]
    response.headers["Vary"] = "Accept-Language"
    response.headers["Link"] = f'<{seo["canonical"]}>; rel="canonical", <{api_url(context)}>; rel="alternate"; type="application/json"'
    response.headers["Content-Security-Policy"] = (
        "default-src 'self'; base-uri 'self'; object-src 'none'; frame-ancestors 'none'; "
        "form-action 'self'; img-src 'self' data: blob: https://*.googlesyndication.com https://*.doubleclick.net https://*.google.com; "
        "font-src 'self' data:; "
        f"style-src 'self' 'unsafe-inline' 'nonce-{nonce}'; style-src-attr 'unsafe-inline'; "
        f"script-src 'self' 'nonce-{nonce}' https://pagead2.googlesyndication.com https://*.googlesyndication.com https://*.doubleclick.net https://*.google.com https://*.googletagservices.com; "
        "script-src-attr 'none'; "
        "connect-src 'self' https://*.googlesyndication.com https://*.doubleclick.net https://*.google.com; "
        "frame-src https://*.googlesyndication.com https://*.doubleclick.net https://*.google.com; "
        "manifest-src 'self'; worker-src 'self' blob:; upgrade-insecure-requests"
    )
    # Revalidate every navigation/reload so the server-rendered Panchang always
    # starts from the current local minute rather than a cached calculation.
    response.headers["Cache-Control"] = "no-cache, max-age=0, must-revalidate"
    response.headers["Pragma"] = "no-cache"
    response.headers["Expires"] = "0"
    response.set_cookie(
        PUSH_CSRF_COOKIE,
        push_csrf,
        max_age=400 * 24 * 60 * 60,
        secure=request.is_secure,
        httponly=False,
        samesite="Strict",
        path="/",
    )
    return response


@app.before_request
def redirect_render_hostname() -> Response | None:
    """Move human and crawler GET requests from Render to the public domain."""
    if request.method not in {"GET", "HEAD"} or request.path == "/health":
        return None
    host = (request.host or "").split(":", 1)[0].lower()
    public_host = (urlsplit(PUBLIC_SITE_URL).hostname or "").lower()
    if host.endswith(".onrender.com") and public_host and host != public_host:
        suffix = request.full_path
        if suffix.endswith("?"):
            suffix = suffix[:-1]
        return redirect(f"{PUBLIC_SITE_URL}{suffix}", code=308)
    return None


@app.after_request
def add_common_headers(response: Response) -> Response:
    response.headers.setdefault("X-Content-Type-Options", "nosniff")
    response.headers.setdefault("Referrer-Policy", "strict-origin-when-cross-origin")
    response.headers.setdefault("Permissions-Policy", "geolocation=(self), camera=(), microphone=(), payment=(), usb=()")
    response.headers.setdefault("Cross-Origin-Opener-Policy", "same-origin-allow-popups")
    response.headers.setdefault("X-Frame-Options", "DENY")
    response.headers.setdefault("X-Robots-Tag", "index, follow, max-image-preview:large, max-snippet:-1")
    return response


@app.get("/")
def home() -> Response:
    if (request.args.get("place") or request.args.get("q")) and not request.args.get("lat"):
        return search_redirect_response()
    return page_response()


@app.get("/<path_lang>/panchang/<place_slug>/<date_str>")
def dated_panchang(path_lang: str, place_slug: str, date_str: str) -> Response:
    return page_response(path_lang, place_slug, date_str)


@app.get("/<path_lang>/panchang/<place_slug>")
def current_panchang(path_lang: str, place_slug: str) -> Response:
    if path_lang not in LANGUAGES or place_slug not in POPULAR_PLACES:
        return plain_not_found()
    place = POPULAR_PLACES[place_slug]
    _tz_name, tz = safe_timezone(str(place["timezone"]))
    current_date = datetime.now(tz).date().isoformat()
    return redirect(f"/{path_lang}/panchang/{place_slug}/{current_date}", code=302)


@app.get("/api/panchang")
def panchang_api() -> Response:
    try:
        context = resolve_context()
        data, _seo, _jsonld = build_payload(context)
        response = jsonify(data)
        response.headers["Content-Language"] = context["lang"]
        response.headers["Access-Control-Allow-Origin"] = "*"
        response.headers["Cache-Control"] = "no-store" if context["live"] else "public, max-age=300"
        response.headers["Content-Security-Policy"] = "default-src 'none'; frame-ancestors 'none'"
        return response
    except Exception as exc:
        app.logger.exception("Panchang API calculation failed")
        response = jsonify({"error": "Panchang calculation failed", "detail": str(exc) if app.debug else ""})
        response.status_code = 500
        response.headers["Cache-Control"] = "no-store"
        return response


def _push_json(payload: dict[str, Any], status: int = 200) -> Response:
    response = jsonify(payload)
    response.status_code = status
    response.headers["Cache-Control"] = "no-store"
    response.headers["X-Robots-Tag"] = "noindex, nofollow"
    response.headers["Content-Security-Policy"] = "default-src 'none'; frame-ancestors 'none'"
    return response


@app.post("/api/push/subscribe")
def push_subscribe_api() -> Response:
    if not push_feature_enabled():
        return _push_json({"error": "Daily push is not configured on the server."}, 503)
    if not validate_push_csrf():
        return _push_json({"error": "The subscription request could not be verified."}, 403)
    payload = request.get_json(silent=True)
    if not isinstance(payload, dict):
        return _push_json({"error": "A JSON request body is required."}, 400)
    subscription = _valid_push_subscription(payload.get("subscription"))
    if subscription is None:
        return _push_json({"error": "The browser push subscription is invalid."}, 400)
    language = str(payload.get("language") or "en").lower().split("-")[0]
    timezone_name = str(payload.get("timezone") or "UTC")[:100]
    target_url = _normalize_push_target(payload.get("target_url"))
    try:
        next_send = upsert_push_subscription(subscription, language, timezone_name, target_url)
    except Exception:
        app.logger.exception("Could not save a Web Push subscription")
        return _push_json({"error": "The daily notification subscription could not be saved."}, 503)
    return _push_json({"ok": True, "next_send_utc": next_send, "local_hour": PUSH_HOUR_LOCAL}, 201)


@app.post("/api/push/unsubscribe")
def push_unsubscribe_api() -> Response:
    if not validate_push_csrf():
        return _push_json({"error": "The unsubscribe request could not be verified."}, 403)
    payload = request.get_json(silent=True) or {}
    endpoint = str(payload.get("endpoint") or "").strip()
    if endpoint:
        try:
            delete_push_subscription(endpoint)
        except Exception:
            app.logger.exception("Could not remove a Web Push subscription")
            return _push_json({"error": "The subscription could not be removed."}, 503)
    return _push_json({"ok": True})


def normalized_search(value: str) -> str:
    return unicodedata.normalize("NFKC", value).casefold().strip()


def local_place_results(query: str) -> list[dict[str, Any]]:
    needle = normalized_search(query)
    matches: list[dict[str, Any]] = []
    for slug, place in POPULAR_PLACES.items():
        haystack = normalized_search(f"{place['name']} {place.get('country', '')} {slug.replace('-', ' ')}")
        if needle in haystack or haystack.startswith(needle):
            matches.append({
                "name": place["name"],
                "display_name": f"{place['name']}, {place.get('country', '')}".strip(", "),
                "latitude": place["latitude"],
                "longitude": place["longitude"],
                "timezone": place["timezone"],
                "country": place.get("country", ""),
                "slug": slug,
                "source": "built-in",
            })
    return matches


@lru_cache(maxsize=512)
def remote_place_results(query: str, lang: str) -> tuple[dict[str, Any], ...]:
    endpoint = os.getenv("GEOCODING_API_URL", "https://geocoding-api.open-meteo.com/v1/search")
    response = requests.get(
        endpoint,
        params={"name": query, "count": 10, "language": lang if lang in LANGUAGES else "en", "format": "json"},
        headers={"Accept": "application/json", "User-Agent": f"{APP_NAME}/{APP_VERSION} (+{site_root()})"},
        timeout=(2.5, 6.0),
    )
    response.raise_for_status()
    payload = response.json()
    output: list[dict[str, Any]] = []
    for place in payload.get("results", [])[:10]:
        try:
            name = str(place["name"]).strip()
            latitude = float(place["latitude"])
            longitude = float(place["longitude"])
        except (KeyError, TypeError, ValueError):
            continue
        timezone_name, _tz = safe_timezone(str(place.get("timezone") or "UTC"), "UTC")
        country = str(place.get("country") or place.get("country_code") or "").strip()
        admin = str(place.get("admin1") or "").strip()
        pieces = [name]
        if admin and normalized_search(admin) != normalized_search(name):
            pieces.append(admin)
        if country:
            pieces.append(country)
        output.append({
            "name": name,
            "display_name": ", ".join(pieces),
            "latitude": round(latitude, 6),
            "longitude": round(longitude, 6),
            "timezone": timezone_name,
            "country": country,
            "country_code": str(place.get("country_code") or ""),
            "admin1": admin,
            "slug": slugify_place(name),
            "source": "Open-Meteo / GeoNames",
        })
    return tuple(output)


def search_redirect_response() -> Response:
    query = re.sub(r"\s+", " ", (request.args.get("place") or request.args.get("q") or "").strip())[:100]
    if len(query) < 2:
        return plain_not_found()
    lang = (request.args.get("lang") or "en").lower().split("-")[0]
    if lang not in LANGUAGES:
        lang = "en"

    local_matches = local_place_results(query)
    exact = next((item for item in local_matches if normalized_search(item["name"]) == normalized_search(query)), None)
    selected = exact or (local_matches[0] if local_matches else None)
    if selected is None:
        try:
            remote = remote_place_results(query, lang)
            selected = remote[0] if remote else None
        except requests.RequestException:
            app.logger.warning("Search redirect geocoding unavailable", exc_info=app.debug)
    if selected is None:
        response = Response(f"No matching place found for: {query}", status=404, mimetype="text/plain")
        response.headers["Cache-Control"] = "no-store"
        return response

    tz_name, tz = safe_timezone(str(selected.get("timezone") or "UTC"), "UTC")
    requested_date = safe_date(request.args.get("date"), datetime.now(tz).date())
    slug = str(selected.get("slug") or slugify_place(str(selected["name"])))
    path = f"/{lang}/panchang/{quote(slug, safe='-')}/{requested_date.isoformat()}"
    params: dict[str, str] = {}
    if slug not in POPULAR_PLACES:
        params = {
            "place": str(selected["name"]),
            "lat": f"{float(selected['latitude']):.6f}",
            "lon": f"{float(selected['longitude']):.6f}",
            "tz": tz_name,
        }
        if selected.get("country"):
            params["country"] = str(selected["country"])
    if request.args.get("time"):
        params["time"] = safe_time(request.args.get("time"), dt_time(12, 0)).strftime("%H:%M")
        params["live"] = "0"
    target = path + (f"?{urlencode(params)}" if params else "")
    response = redirect(target, code=302)
    response.headers["Cache-Control"] = "no-store"
    return response


@app.get("/search")
def search_page() -> Response:
    return search_redirect_response()


@app.get("/api/places")
def places_api() -> Response:
    query = re.sub(r"\s+", " ", (request.args.get("q") or "").strip())[:100]
    lang = (request.args.get("lang") or "en").lower().split("-")[0]
    if len(query) < 2:
        response = jsonify({"query": query, "results": []})
        response.headers["Cache-Control"] = "no-store"
        return response

    combined = local_place_results(query)
    try:
        combined.extend(remote_place_results(query, lang))
    except requests.RequestException:
        app.logger.warning("Remote place search unavailable", exc_info=app.debug)

    deduplicated: list[dict[str, Any]] = []
    seen: set[tuple[int, int]] = set()
    for place in combined:
        key = (round(float(place["latitude"]) * 100), round(float(place["longitude"]) * 100))
        if key in seen:
            continue
        seen.add(key)
        deduplicated.append(place)
        if len(deduplicated) >= 10:
            break

    response = jsonify({
        "query": query,
        "results": deduplicated,
        "attribution": "GeoNames data via Open-Meteo Geocoding API; built-in results are maintained by this application.",
    })
    response.headers["Cache-Control"] = "public, max-age=86400"
    response.headers["Content-Security-Policy"] = "default-src 'none'; frame-ancestors 'none'"
    return response



def haversine_km(latitude_a: float, longitude_a: float, latitude_b: float, longitude_b: float) -> float:
    radius_km = 6371.0088
    phi_a = math.radians(latitude_a)
    phi_b = math.radians(latitude_b)
    delta_phi = math.radians(latitude_b - latitude_a)
    delta_lambda = math.radians(longitude_b - longitude_a)
    value = math.sin(delta_phi / 2) ** 2 + math.cos(phi_a) * math.cos(phi_b) * math.sin(delta_lambda / 2) ** 2
    return radius_km * 2 * math.atan2(math.sqrt(value), math.sqrt(max(0.0, 1.0 - value)))


def nearest_builtin_place(latitude: float, longitude: float, maximum_km: float = 35.0) -> dict[str, Any] | None:
    nearest: tuple[float, str, dict[str, Any]] | None = None
    for slug, place in POPULAR_PLACES.items():
        distance = haversine_km(latitude, longitude, float(place["latitude"]), float(place["longitude"]))
        if nearest is None or distance < nearest[0]:
            nearest = (distance, slug, place)
    if nearest is None or nearest[0] > maximum_km:
        return None
    distance, slug, place = nearest
    return {
        "name": str(place["name"]),
        "city": str(place["name"]),
        "country": str(place.get("country") or ""),
        "slug": slug,
        "distance_km": round(distance, 1),
        "source": "built-in",
    }


@lru_cache(maxsize=2048)
def reverse_geocode_result(latitude_key: float, longitude_key: float, lang: str) -> dict[str, Any]:
    latitude = float(latitude_key)
    longitude = float(longitude_key)
    local_match = nearest_builtin_place(latitude, longitude)
    if local_match is not None:
        return local_match

    language = lang if lang in LANGUAGES else "en"
    site_identity = os.getenv("REVERSE_GEOCODING_CONTACT", "").strip() or PUBLIC_SITE_URL
    user_agent = f"{APP_NAME}/{APP_VERSION} (+{site_identity})"
    endpoint = os.getenv("REVERSE_GEOCODING_API_URL", "https://nominatim.openstreetmap.org/reverse")

    try:
        response = requests.get(
            endpoint,
            params={
                "format": "jsonv2",
                "lat": f"{latitude:.6f}",
                "lon": f"{longitude:.6f}",
                "zoom": 12,
                "addressdetails": 1,
                "accept-language": language,
            },
            headers={"Accept": "application/json", "User-Agent": user_agent},
            timeout=(2.5, 6.5),
        )
        response.raise_for_status()
        payload = response.json()
        address = payload.get("address") or {}
        locality_keys = (
            "city", "town", "village", "municipality", "hamlet", "suburb",
            "city_district", "county", "state_district", "state",
        )
        name = next((str(address.get(key) or "").strip() for key in locality_keys if str(address.get(key) or "").strip()), "")
        if not name:
            name = str(payload.get("name") or "").strip()
        if not name:
            name = str(payload.get("display_name") or "").split(",", 1)[0].strip()
        if name:
            return {
                "name": name[:120],
                "city": name[:120],
                "country": str(address.get("country") or "").strip()[:80],
                "country_code": str(address.get("country_code") or "").upper()[:3],
                "slug": slugify_place(name),
                "source": "OpenStreetMap Nominatim",
            }
    except (requests.RequestException, ValueError, TypeError):
        app.logger.warning("Primary reverse geocoding unavailable", exc_info=app.debug)

    # Keyless fallback intended for low-volume client-location naming.
    try:
        fallback_response = requests.get(
            "https://api.bigdatacloud.net/data/reverse-geocode-client",
            params={
                "latitude": f"{latitude:.6f}",
                "longitude": f"{longitude:.6f}",
                "localityLanguage": language,
            },
            headers={"Accept": "application/json", "User-Agent": user_agent},
            timeout=(2.5, 6.5),
        )
        fallback_response.raise_for_status()
        payload = fallback_response.json()
        name = str(payload.get("city") or payload.get("locality") or payload.get("principalSubdivision") or "").strip()
        if name:
            return {
                "name": name[:120],
                "city": name[:120],
                "country": str(payload.get("countryName") or "").strip()[:80],
                "country_code": str(payload.get("countryCode") or "").upper()[:3],
                "slug": slugify_place(name),
                "source": "BigDataCloud",
            }
    except (requests.RequestException, ValueError, TypeError):
        app.logger.warning("Fallback reverse geocoding unavailable", exc_info=app.debug)

    broader_match = nearest_builtin_place(latitude, longitude, maximum_km=300.0)
    if broader_match is not None:
        return broader_match
    coordinate_name = f"{latitude:.2f}, {longitude:.2f}"
    return {
        "name": coordinate_name,
        "city": coordinate_name,
        "country": "",
        "slug": slugify_place(coordinate_name),
        "source": "coordinates",
    }


@app.get("/api/reverse-geocode")
def reverse_geocode_api() -> Response:
    latitude = clamp_float(request.args.get("lat"), float(DEFAULT_PLACE["latitude"]), -89.8, 89.8)
    longitude = clamp_float(request.args.get("lon"), float(DEFAULT_PLACE["longitude"]), -180.0, 180.0)
    lang = (request.args.get("lang") or "en").lower().split("-")[0]
    result = dict(reverse_geocode_result(round(latitude, 3), round(longitude, 3), lang))
    result.update({"latitude": round(latitude, 6), "longitude": round(longitude, 6)})
    response = jsonify(result)
    response.headers["Cache-Control"] = "public, max-age=86400, stale-while-revalidate=604800"
    response.headers["Access-Control-Allow-Origin"] = "*"
    response.headers["Content-Security-Policy"] = "default-src 'none'; frame-ancestors 'none'"
    return response


@app.get("/ads.txt")
def ads_txt() -> Response:
    response = Response(
        "google.com, pub-4357913188792813, DIRECT, f08c47fec0942fa0\n",
        mimetype="text/plain",
    )
    response.headers["Cache-Control"] = "public, max-age=86400"
    return response


@app.get("/robots.txt")
def robots_txt() -> Response:
    root = site_root()
    body = "\n".join([
        "User-agent: *",
        "Allow: /",
        "Disallow: /health",
        "",
        f"Sitemap: {root}/sitemap.xml",
        "",
    ])
    response = Response(body, mimetype="text/plain")
    response.headers["Cache-Control"] = "public, max-age=3600"
    return response


@app.get("/sitemap.xml")
def sitemap_xml() -> Response:
    """Return a sitemap index with one child sitemap per language."""
    root = site_root()
    today = datetime.now(IST).date().isoformat()
    entries = [
        '<?xml version="1.0" encoding="UTF-8"?>',
        '<sitemapindex xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">',
        '  <sitemap>',
        f'    <loc>{html.escape(root + "/sitemap-static.xml", quote=True)}</loc>',
        '  </sitemap>',
    ]
    for lang in LANGUAGES:
        entries.extend([
            '  <sitemap>',
            f'    <loc>{html.escape(root + f"/sitemap-{lang}.xml", quote=True)}</loc>',
            f'    <lastmod>{today}</lastmod>',
            '  </sitemap>',
        ])
    entries.append('</sitemapindex>')
    response = Response("\n".join(entries), mimetype="application/xml")
    response.headers["Cache-Control"] = "public, max-age=3600"
    response.headers["Content-Security-Policy"] = "default-src 'none'; frame-ancestors 'none'"
    return response


@app.get("/sitemap-static.xml")
def sitemap_static_xml() -> Response:
    root = site_root()
    entries = [
        '<?xml version="1.0" encoding="UTF-8"?>',
        '<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">',
        '  <url>',
        f'    <loc>{html.escape(root + "/", quote=True)}</loc>',
        '  </url>',
        '</urlset>',
    ]
    response = Response("\n".join(entries), mimetype="application/xml")
    response.headers["Cache-Control"] = "public, max-age=3600"
    response.headers["Content-Security-Policy"] = "default-src 'none'; frame-ancestors 'none'"
    return response


@app.get("/sitemap-<lang>.xml")
def sitemap_language_xml(lang: str) -> Response:
    """Return localized URLs plus reciprocal hreflang alternatives."""
    if lang not in LANGUAGES:
        return plain_not_found()
    root = site_root()
    entries: list[str] = [
        '<?xml version="1.0" encoding="UTF-8"?>',
        '<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9" xmlns:xhtml="http://www.w3.org/1999/xhtml">',
    ]
    # Generate the current date window in each place's own timezone instead of
    # assuming that every indexed city shares India's calendar date.
    for slug, place in POPULAR_PLACES.items():
        _tz_name, place_tz = safe_timezone(str(place["timezone"]))
        place_today = datetime.now(place_tz).date()
        dates = [place_today - timedelta(days=1)] + [place_today + timedelta(days=offset) for offset in range(0, 31)]
        for day in dates:
            loc = f"{root}/{lang}/panchang/{slug}/{day.isoformat()}"
            entries.extend([
                "  <url>",
                f"    <loc>{html.escape(loc, quote=True)}</loc>",
            ])
            for alternate_lang in LANGUAGES:
                alternate_url = f"{root}/{alternate_lang}/panchang/{slug}/{day.isoformat()}"
                entries.append(
                    f'    <xhtml:link rel="alternate" hreflang="{alternate_lang}" href="{html.escape(alternate_url, quote=True)}" />'
                )
            english_url = f"{root}/en/panchang/{slug}/{day.isoformat()}"
            entries.extend([
                f'    <xhtml:link rel="alternate" hreflang="x-default" href="{html.escape(english_url, quote=True)}" />',
                "  </url>",
            ])
    entries.append("</urlset>")
    response = Response("\n".join(entries), mimetype="application/xml")
    response.headers["Cache-Control"] = "public, max-age=3600"
    response.headers["Content-Security-Policy"] = "default-src 'none'; frame-ancestors 'none'"
    return response


@app.get("/manifest.webmanifest")
def web_manifest() -> Response:
    manifest = {
        "id": "/",
        "name": f"{APP_NAME} — Live Local Panchang",
        "short_name": APP_NAME,
        "description": "A location-aware Panchang with Tithi, Nakshatra, Yoga, Karana, Choghadiya, Hora, Muhurta and Lagna timelines.",
        "start_url": "/",
        "scope": "/",
        "display": "standalone",
        "display_override": ["window-controls-overlay", "standalone", "minimal-ui"],
        "orientation": "any",
        "background_color": "#f2f4f9",
        "theme_color": "#35498f",
        "lang": "en-IN",
        "dir": "ltr",
        "categories": ["lifestyle", "utilities", "education"],
        "icons": [
            {"src": "/icon-192.png", "sizes": "192x192", "type": "image/png", "purpose": "any maskable"},
            {"src": "/icon-512.png", "sizes": "512x512", "type": "image/png", "purpose": "any maskable"},
        ],
        "shortcuts": [
            {"name": "Ujjain Panchang", "short_name": "Ujjain", "url": "/en/panchang/ujjain", "icons": [{"src": "/icon-192.png", "sizes": "192x192"}]},
            {"name": "Use current location", "short_name": "My place", "url": "/?live=1", "icons": [{"src": "/icon-192.png", "sizes": "192x192"}]},
        ],
    }
    response = jsonify(manifest)
    response.mimetype = "application/manifest+json"
    response.headers["Cache-Control"] = "public, max-age=86400"
    response.headers["Content-Security-Policy"] = "default-src 'none'; frame-ancestors 'none'"
    return response


@app.get("/sw.js")
def service_worker() -> Response:
    script = rf"""'use strict';
const CACHE = 'panchang-shell-{APP_VERSION}';
const SHELL = ['/', '/manifest.webmanifest', '/icon-192.png', '/icon-512.png', '/badge-96.png', '/favicon.ico'];
self.addEventListener('install', event => {{
  event.waitUntil(caches.open(CACHE).then(cache => cache.addAll(SHELL)).then(() => self.skipWaiting()));
}});
self.addEventListener('activate', event => {{
  event.waitUntil(caches.keys().then(keys => Promise.all(keys.filter(key => key !== CACHE).map(key => caches.delete(key)))).then(() => self.clients.claim()));
}});
self.addEventListener('fetch', event => {{
  const request = event.request;
  if (request.method !== 'GET') return;
  const url = new URL(request.url);
  if (url.origin !== self.location.origin || url.pathname.startsWith('/api/') || url.pathname === '/og.png') return;
  if (request.mode === 'navigate') {{
    event.respondWith(fetch(request).then(response => {{
      const copy = response.clone();
      caches.open(CACHE).then(cache => cache.put(request, copy));
      return response;
    }}).catch(() => caches.match(request).then(hit => hit || caches.match('/'))));
    return;
  }}
  if (/\.(?:png|ico|webmanifest)$/.test(url.pathname)) {{
    event.respondWith(caches.match(request).then(hit => hit || fetch(request).then(response => {{
      const copy = response.clone();
      caches.open(CACHE).then(cache => cache.put(request, copy));
      return response;
    }})));
  }}
}});
self.addEventListener('push', event => {{
  let payload = {{}};
  try {{ payload = event.data ? event.data.json() : {{}}; }} catch (_) {{ payload = {{}}; }}
  const title = payload.title || "Today's Panchang";
  const options = {{
    icon: payload.icon || '/icon-512.png',
    badge: payload.badge || '/badge-96.png',
    tag: 'daily-panchang',
    renotify: false,
    silent: false,
    timestamp: Number(payload.timestamp) || Date.now(),
    lang: payload.lang || 'en',
    data: {{url: payload.url || '/'}}
  }};
  event.waitUntil(self.registration.showNotification(title, options));
}});
self.addEventListener('notificationclick', event => {{
  event.notification.close();
  const target = new URL(event.notification.data?.url || '/', self.location.origin).href;
  event.waitUntil(self.clients.matchAll({{type: 'window', includeUncontrolled: true}}).then(async clientList => {{
    for (const client of clientList) {{
      try {{
        if (new URL(client.url).origin !== self.location.origin) continue;
        if ('navigate' in client) await client.navigate(target);
        return client.focus();
      }} catch (_) {{ /* Try another matching client. */ }}
    }}
    return self.clients.openWindow ? self.clients.openWindow(target) : undefined;
  }}));
}});
"""
    response = Response(script, mimetype="application/javascript")
    response.headers["Service-Worker-Allowed"] = "/"
    response.headers["Cache-Control"] = "no-cache"
    response.headers["Content-Security-Policy"] = "default-src 'self'; script-src 'self'; connect-src 'self'; object-src 'none'"
    return response


# ---------------------------------------------------------------------------
# Dynamic social preview image
# ---------------------------------------------------------------------------

_SOCIAL_SCRIPT_NAMES = {
    "hi": "Devanagari", "mr": "Devanagari", "ne": "Devanagari", "sa": "Devanagari",
    "gu": "Gujarati", "bn": "Bengali", "ta": "Tamil", "te": "Telugu", "kn": "Kannada",
    "ml": "Malayalam", "pa": "Gurmukhi", "or": "Oriya",
}
_SOCIAL_FONT_FAMILIES = {
    "Devanagari": "NotoSansDevanagari", "Gujarati": "NotoSansGujarati", "Bengali": "NotoSansBengali",
    "Tamil": "NotoSansTamil", "Telugu": "NotoSansTelugu", "Kannada": "NotoSansKannada",
    "Malayalam": "NotoSansMalayalam", "Gurmukhi": "NotoSansGurmukhi", "Oriya": "NotoSansOriya",
}
_SOCIAL_SCRIPT_RANGES = {
    "Devanagari": ((0x0900, 0x097F), (0x1CD0, 0x1CFF), (0xA8E0, 0xA8FF)),
    "Bengali": ((0x0980, 0x09FF),), "Gurmukhi": ((0x0A00, 0x0A7F),),
    "Gujarati": ((0x0A80, 0x0AFF),), "Oriya": ((0x0B00, 0x0B7F),),
    "Tamil": ((0x0B80, 0x0BFF),), "Telugu": ((0x0C00, 0x0C7F),),
    "Kannada": ((0x0C80, 0x0CFF),), "Malayalam": ((0x0D00, 0x0D7F),),
}


def _font_layout() -> Any:
    return getattr(getattr(ImageFont, "Layout", object()), "RAQM", None) if ImageFont is not None else None


@lru_cache(maxsize=32)
def _download_social_font(script: str, bold: bool) -> str:
    """Download an OFL Noto TTF to ephemeral storage when Render lacks Indic fonts."""
    if os.getenv("PANCHANG_FONT_DOWNLOAD", "1").strip().lower() in {"0", "false", "no"}:
        return ""
    family = _SOCIAL_FONT_FAMILIES.get(script)
    if not family:
        return ""
    weight = "Bold" if bold else "Regular"
    cache_dir = os.getenv("PANCHANG_FONT_CACHE_DIR", "/tmp/panchang-fonts")
    target = os.path.join(cache_dir, f"{family}-{weight}.ttf")
    try:
        if os.path.getsize(target) > 10_000:
            return target
    except OSError:
        pass
    url = (
        "https://raw.githubusercontent.com/notofonts/noto-fonts/main/hinted/ttf/"
        f"{family}/{family}-{weight}.ttf"
    )
    try:
        os.makedirs(cache_dir, exist_ok=True)
        response = requests.get(
            url,
            headers={"User-Agent": f"{APP_NAME}/{APP_VERSION}", "Accept": "application/octet-stream"},
            timeout=(2.5, 6),
        )
        response.raise_for_status()
        payload = response.content
        if len(payload) < 10_000 or payload[:4] not in {b"\x00\x01\x00\x00", b"OTTO", b"true", b"ttcf"}:
            return ""
        temporary = f"{target}.{os.getpid()}.tmp"
        with open(temporary, "wb") as font_file:
            font_file.write(payload)
        os.replace(temporary, target)
        return target
    except (OSError, requests.RequestException):
        app.logger.warning("Could not prepare social font %s", family, exc_info=app.debug)
        return ""


@lru_cache(maxsize=512)
def social_font(lang: str, size: int, bold: bool = False) -> Any:
    """Load a shaped local font, with a cached Noto fallback for Indic scripts."""
    if ImageFont is None:
        return None
    candidates: list[str] = []
    script = _SOCIAL_SCRIPT_NAMES.get(lang)
    weight = "Bold" if bold else "Regular"
    if script:
        family = _SOCIAL_FONT_FAMILIES.get(script, f"NotoSans{script}")
        lohit_paths = {
            "Devanagari": "/usr/share/fonts/truetype/lohit-devanagari/Lohit-Devanagari.ttf",
            "Gujarati": "/usr/share/fonts/truetype/lohit-gujarati/Lohit-Gujarati.ttf",
            "Bengali": "/usr/share/fonts/truetype/lohit-bengali/Lohit-Bengali.ttf",
            "Tamil": "/usr/share/fonts/truetype/lohit-tamil/Lohit-Tamil.ttf",
            "Telugu": "/usr/share/fonts/truetype/lohit-telugu/Lohit-Telugu.ttf",
            "Kannada": "/usr/share/fonts/truetype/lohit-kannada/Lohit-Kannada.ttf",
            "Malayalam": "/usr/share/fonts/truetype/lohit-malayalam/Lohit-Malayalam.ttf",
            "Oriya": "/usr/share/fonts/truetype/lohit-oriya/Lohit-Odia.ttf",
        }
        if script in lohit_paths:
            candidates.append(lohit_paths[script])
        candidates.extend([
            f"/usr/share/fonts/truetype/noto/{family}-{weight}.ttf",
            f"/usr/share/fonts/opentype/noto/{family}-{weight}.ttf",
            f"/usr/share/fonts/truetype/noto/{family}UI-{weight}.ttf",
        ])
        candidates.extend(sorted(glob.glob(f"/usr/share/fonts/**/*{family}*{weight}*.ttf", recursive=True)))
    else:
        candidates.extend([
            "/usr/share/fonts/opentype/inter/InterDisplay-ExtraBold.otf" if bold else "/usr/share/fonts/opentype/inter/Inter-Regular.otf",
            "/usr/share/fonts/opentype/inter/Inter-Bold.otf" if bold else "/usr/share/opentype/inter/Inter-Regular.otf",
            "/usr/share/fonts/truetype/noto/NotoSans-Bold.ttf" if bold else "/usr/share/fonts/truetype/noto/NotoSans-Regular.ttf",
        ])
    candidates.extend([
        "/usr/share/opentype/freefont/FreeSansBold.otf" if bold else "/usr/share/opentype/freefont/FreeSans.otf",
        "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf" if bold else "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
    ])
    layout = _font_layout()

    def load_candidate(font_path: str) -> Any | None:
        if not font_path or not os.path.exists(font_path):
            return None
        try:
            kwargs = {"layout_engine": layout} if layout is not None else {}
            return ImageFont.truetype(font_path, size=size, **kwargs)
        except Exception:
            if layout is not None:
                try:
                    return ImageFont.truetype(font_path, size=size)
                except Exception:
                    pass
            return None

    # Prefer installed fonts so the first social-crawler request remains fast.
    # Download the matching OFL Noto face only when this environment genuinely
    # lacks the requested Indic script.
    for font_path in dict.fromkeys(candidates):
        loaded = load_candidate(font_path)
        if loaded is not None:
            return loaded
    if script:
        loaded = load_candidate(_download_social_font(script, bold))
        if loaded is not None:
            return loaded
    try:
        return ImageFont.load_default(size=size)
    except TypeError:
        return ImageFont.load_default()


def _is_script_character(character: str, lang: str) -> bool:
    script = _SOCIAL_SCRIPT_NAMES.get(lang)
    codepoint = ord(character)
    return any(start <= codepoint <= end for start, end in _SOCIAL_SCRIPT_RANGES.get(script, ()))


def social_runs(text: str, lang: str) -> list[tuple[str, bool]]:
    """Split mixed native-script/Latin strings so each run gets a suitable font."""
    if lang == "en" or lang not in _SOCIAL_SCRIPT_NAMES:
        return [(text, False)]
    runs: list[tuple[str, bool]] = []
    buffer = ""
    active: bool | None = None
    for character in text:
        if character in {"\u200c", "\u200d"} or unicodedata.combining(character):
            use_script = active if active is not None else True
        elif character.isspace():
            use_script = active if active is not None else False
        else:
            use_script = _is_script_character(character, lang)
        if active is None or use_script == active:
            buffer += character
            active = use_script
        else:
            runs.append((buffer, bool(active)))
            buffer = character
            active = use_script
    if buffer:
        runs.append((buffer, bool(active)))
    return runs


def social_run_width(draw: Any, text: str, lang: str, size: int, bold: bool = False) -> float:
    width = 0.0
    for run, use_script in social_runs(text, lang):
        font = social_font(lang if use_script else "en", size, bold)
        try:
            width += float(draw.textlength(run, font=font))
        except Exception:
            box = draw.textbbox((0, 0), run, font=font)
            width += float(box[2] - box[0])
    return width


def fit_social_size(draw: Any, text: str, lang: str, max_width: float, max_size: int, min_size: int, bold: bool = False) -> int:
    for size in range(max_size, min_size - 1, -1):
        if social_run_width(draw, text, lang, size, bold) <= max_width:
            return size
    return min_size


def truncate_social_mixed(draw: Any, text: str, lang: str, size: int, max_width: float, bold: bool = False) -> str:
    if social_run_width(draw, text, lang, size, bold) <= max_width:
        return text
    ellipsis = "…"
    characters = list(text)
    while characters and social_run_width(draw, "".join(characters).rstrip() + ellipsis, lang, size, bold) > max_width:
        characters.pop()
    return ("".join(characters).rstrip() + ellipsis) if characters else ellipsis


def draw_social_mixed(
    draw: Any,
    position: tuple[float, float],
    text: str,
    lang: str,
    size: int,
    bold: bool,
    fill: tuple[int, int, int, int],
    max_width: float | None = None,
) -> str:
    rendered = truncate_social_mixed(draw, text, lang, size, max_width, bold) if max_width else text
    x, y = position
    for run, use_script in social_runs(rendered, lang):
        font = social_font(lang if use_script else "en", size, bold)
        try:
            box = draw.textbbox((0, 0), run, font=font)
            draw.text((x - box[0], y - box[1]), run, font=font, fill=fill)
            advance = float(draw.textlength(run, font=font))
        except Exception:
            draw.text((x, y), run, font=font, fill=fill)
            advance = float(draw.textbbox((0, 0), run, font=font)[2])
        x += advance
    return rendered


def _mix_rgb(first: tuple[int, int, int], second: tuple[int, int, int], amount: float) -> tuple[int, int, int, int]:
    return (
        round(first[0] + (second[0] - first[0]) * amount),
        round(first[1] + (second[1] - first[1]) * amount),
        round(first[2] + (second[2] - first[2]) * amount),
        255,
    )


def _draw_social_sun(draw: Any, center: tuple[int, int], radius: int, color: tuple[int, int, int, int]) -> None:
    cx, cy = center
    for angle in range(0, 360, 45):
        radians = math.radians(angle)
        x1 = cx + math.cos(radians) * (radius + 7)
        y1 = cy + math.sin(radians) * (radius + 7)
        x2 = cx + math.cos(radians) * (radius + 16)
        y2 = cy + math.sin(radians) * (radius + 16)
        draw.line((x1, y1, x2, y2), fill=color, width=3)
    draw.ellipse((cx - radius, cy - radius, cx + radius, cy + radius), outline=color, width=4)
    draw.ellipse((cx - 5, cy - 5, cx + 5, cy + 5), fill=color)


def render_social_image(context: dict[str, Any], data: dict[str, Any]) -> bytes:
    """Render a balanced, modern 1200×630 social share card."""
    if Image is None or ImageDraw is None or ImageFont is None:
        return base64.b64decode(OG_IMAGE_B64)

    width, height = 1200, 630
    canvas = Image.new("RGBA", (width, height), (243, 245, 251, 255))

    ink = (24, 32, 51, 255)
    muted = (101, 113, 135, 255)
    paper = (255, 255, 255, 255)
    soft = (238, 241, 248, 255)
    line = (215, 220, 232, 255)
    accent = (92, 100, 216, 255)
    accent_deep = (65, 73, 184, 255)
    teal = (23, 139, 156, 255)
    good = (23, 138, 104, 255)
    good_soft = (237, 248, 244, 255)
    bad = (202, 77, 101, 255)
    bad_soft = (255, 240, 243, 255)
    mixed = (173, 116, 29, 255)
    mixed_soft = (255, 247, 232, 255)
    margin = 30

    # Quiet ambient color keeps the card lively without competing with data.
    ambient_layer = Image.new("RGBA", (width, height), (0, 0, 0, 0))
    ambient_draw = ImageDraw.Draw(ambient_layer)
    ambient_draw.ellipse((870, -220, 1320, 230), fill=(92, 100, 216, 18))
    ambient_draw.ellipse((-190, 360, 240, 790), fill=(23, 139, 156, 14))
    canvas = Image.alpha_composite(canvas, ambient_layer)

    # Soft shadow and a restrained indigo-to-teal masthead.
    header_box = (margin, 22, width - margin, 144)
    shadow_layer = Image.new("RGBA", (width, height), (0, 0, 0, 0))
    shadow_draw = ImageDraw.Draw(shadow_layer)
    shadow_draw.rounded_rectangle((margin, 29, width - margin, 151), radius=28, fill=(35, 43, 78, 42))
    shadow_layer = shadow_layer.filter(ImageFilter.GaussianBlur(13))
    canvas = Image.alpha_composite(canvas, shadow_layer)

    header_width = header_box[2] - header_box[0]
    header_height = header_box[3] - header_box[1]
    gradient = Image.new("RGBA", (header_width, header_height), (0, 0, 0, 0))
    gradient_draw = ImageDraw.Draw(gradient)
    left_color = (69, 77, 186)
    right_color = (28, 116, 132)
    for x in range(header_width):
        amount = x / max(1, header_width - 1)
        color = _mix_rgb(left_color, right_color, amount)
        gradient_draw.line((x, 0, x, header_height), fill=color)
    header_mask = Image.new("L", (header_width, header_height), 0)
    ImageDraw.Draw(header_mask).rounded_rectangle((0, 0, header_width - 1, header_height - 1), radius=28, fill=255)
    canvas.paste(gradient, (header_box[0], header_box[1]), header_mask)
    draw = ImageDraw.Draw(canvas)

    icon_box = (50, 42, 132, 124)
    draw.rounded_rectangle(icon_box, radius=22, fill=(255, 255, 255, 235), outline=(255, 255, 255, 245), width=2)
    _draw_social_sun(draw, (91, 83), 13, accent_deep)

    lang = context["lang"]
    title_text = f"{tr(lang, 'panchang')}  •  {context['place']}"
    title_size = fit_social_size(draw, title_text, lang, 820, 47, 29, True)
    draw_social_mixed(draw, (153, 40), title_text, lang, title_size, True, paper, 820)

    subtitle = f"{format_date_label(context['date'], lang)}  •  {format_clock(context['at'])}  •  {context['timezone']}"
    subtitle_size = fit_social_size(draw, subtitle, lang, 865, 25, 17, True)
    draw_social_mixed(draw, (154, 98), subtitle, lang, subtitle_size, True, (225, 232, 246, 255), 865)

    live_text = tr(lang, "live")
    live_size = 15
    live_width = social_run_width(draw, live_text, lang, live_size, True)
    live_left = width - margin - live_width - 54
    draw.rounded_rectangle((live_left, 52, width - margin - 16, 88), radius=18, fill=(255, 255, 255, 238))
    draw.ellipse((live_left + 13, 66, live_left + 21, 74), fill=teal)
    draw_social_mixed(draw, (live_left + 27, 60), live_text, lang, live_size, True, accent_deep)

    card_gap_x = 12
    card_gap_y = 10
    card_width = int((width - margin * 2 - card_gap_x * 2) / 3)
    cards_top = 158
    card_height = 138

    # One shared shadow layer is faster and gives the grid a clean floating feel.
    card_shadow = Image.new("RGBA", (width, height), (0, 0, 0, 0))
    card_shadow_draw = ImageDraw.Draw(card_shadow)
    for index in range(min(9, len(data.get("sections", [])))):
        column = index % 3
        row = index // 3
        x1 = margin + column * (card_width + card_gap_x)
        y1 = cards_top + row * (card_height + card_gap_y)
        card_shadow_draw.rounded_rectangle((x1, y1 + 5, x1 + card_width, y1 + card_height + 5), radius=18, fill=(39, 48, 83, 24))
    card_shadow = card_shadow.filter(ImageFilter.GaussianBlur(9))
    canvas = Image.alpha_composite(canvas, card_shadow)
    draw = ImageDraw.Draw(canvas)

    for index, section in enumerate(data["sections"][:9]):
        column = index % 3
        row = index // 3
        x1 = margin + column * (card_width + card_gap_x)
        y1 = cards_top + row * (card_height + card_gap_y)
        x2 = x1 + card_width
        y2 = y1 + card_height
        item = current_or_focused(section.get("items", []))
        quality = item.get("quality", "neutral") if item else "neutral"
        is_mixed = bool(item and item.get("detail") == data.get("ui", {}).get("mixed"))

        border = line
        border_width = 2
        status_text = ""
        status_color = accent
        status_fill = soft
        if quality == "auspicious":
            border = good
            border_width = 4
            status_text = tr(lang, "good")
            status_color = good
            status_fill = good_soft
        elif quality == "inauspicious":
            border = bad
            border_width = 4
            status_text = tr(lang, "avoid")
            status_color = bad
            status_fill = bad_soft
        elif is_mixed:
            border = mixed
            border_width = 4
            status_text = tr(lang, "mixed")
            status_color = mixed
            status_fill = mixed_soft

        draw.rounded_rectangle((x1, y1, x2, y2), radius=18, fill=paper, outline=border, width=border_width)
        if not status_text:
            draw.rounded_rectangle((x1 + 14, y1 + 14, x1 + 20, y1 + 39), radius=3, fill=accent)

        label_left = x1 + (30 if not status_text else 20)
        label = str(section.get("label", ""))
        label_size = fit_social_size(draw, label, lang, 225, 16, 11, True)
        draw_social_mixed(draw, (label_left, y1 + 12), label, lang, label_size, True, muted, 225)

        if status_text:
            badge_size = fit_social_size(draw, status_text, lang, 118, 12, 9, True)
            status_text = truncate_social_mixed(draw, status_text, lang, badge_size, 118, True)
            badge_width = social_run_width(draw, status_text, lang, badge_size, True) + 22
            badge_left = x2 - badge_width - 13
            draw.rounded_rectangle((badge_left, y1 + 9, x2 - 13, y1 + 34), radius=13, fill=status_fill, outline=status_color, width=1)
            draw_social_mixed(draw, (badge_left + 11, y1 + 14), status_text, lang, badge_size, True, status_color, 118)

        value = str(item.get("title", "—") if item else "—")
        value_size = fit_social_size(draw, value, lang, card_width - 40, 25, 17, True)
        draw_social_mixed(draw, (x1 + 20, y1 + 44), value, lang, value_size, True, ink, card_width - 40)

        crosses_day = bool(item and item.get("crosses_day") and item.get("start_display") and item.get("end_display"))
        card_date = str(item.get("start_display", "") if crosses_day else item.get("date", "") if item else "")
        date_size = fit_social_size(draw, card_date, lang, card_width - 40, 14, 10, True)
        draw_social_mixed(draw, (x1 + 20, y1 + 88), card_date, lang, date_size, True, muted, card_width - 40)

        clock = str(("→ " + item.get("end_display", "")) if crosses_day else item.get("clock", item.get("time", "")) if item else "")
        clock_size = fit_social_size(draw, clock, lang, card_width - 40, 15, 10, False)
        draw_social_mixed(draw, (x1 + 20, y1 + 111), clock, lang, clock_size, False, muted, card_width - 40)

    footer_y = 598
    draw.line((margin + 7, footer_y - 10, width - margin - 7, footer_y - 10), fill=line, width=1)
    site_text = site_root().replace("https://", "").replace("http://", "").split("/")[0] or APP_NAME
    draw_social_mixed(draw, (margin + 8, footer_y), site_text, "en", 15, True, accent_deep)
    footer_message = f"{tr(lang, 'live')} • {TIMELINE_FUTURE_ITEMS}+ {tr(lang, 'upcoming_values')}"
    footer_size = fit_social_size(draw, footer_message, lang, 450, 15, 10, True)
    footer_width = social_run_width(draw, footer_message, lang, footer_size, True)
    draw_social_mixed(draw, (width - margin - 8 - footer_width, footer_y), footer_message, lang, footer_size, True, muted, 450)

    output = io.BytesIO()
    canvas.convert("RGB").save(output, format="PNG", optimize=True)
    return output.getvalue()

def embedded_asset(encoded: str, mimetype: str, filename: str) -> Response:
    response = Response(base64.b64decode(encoded), mimetype=mimetype)
    response.headers["Content-Disposition"] = f'inline; filename="{filename}"'
    response.headers["Cache-Control"] = "public, max-age=31536000, immutable"
    response.headers["Content-Security-Policy"] = "default-src 'none'; frame-ancestors 'none'"
    return response


@app.get("/icon-192.png")
def icon_192() -> Response:
    return embedded_asset(ICON_192_B64, "image/png", "panchang-192.png")


@app.get("/icon-512.png")
def icon_512() -> Response:
    return embedded_asset(ICON_512_B64, "image/png", "panchang-512.png")


@app.get("/badge-96.png")
def badge_96() -> Response:
    return embedded_asset(BADGE_96_B64, "image/png", "panchang-badge-96.png")


@app.get("/og.png")
@app.get("/og/<snapshot>.png")
@app.get("/og/<path_lang>/<snapshot>.png")
def open_graph_image(snapshot: str | None = None, path_lang: str | None = None) -> Response:
    if path_lang and path_lang not in LANGUAGES:
        return plain_not_found()
    try:
        # Only this renderer accepts the explicit minute in the query. Keeping
        # the language in the route prevents cross-language social cache hits.
        context = resolve_context(path_lang, allow_snapshot_time=True)
        context["social_live"] = True
        data = build_panchang(context)
        payload = render_social_image(context, data)
        response = Response(payload, mimetype="image/png")
        response.headers["Cache-Control"] = "public, max-age=86400, stale-while-revalidate=604800"
        response.headers["Content-Language"] = context["lang"]
        response.headers["Vary"] = "Accept-Language"
        response.headers["Content-Disposition"] = f'inline; filename="panchang-{context["lang"]}-{snapshot or "live"}.png"'
        response.headers["Accept-Ranges"] = "bytes"
        response.headers["X-Content-Type-Options"] = "nosniff"
        response.headers["Access-Control-Allow-Origin"] = "*"
        response.headers["Cross-Origin-Resource-Policy"] = "cross-origin"
        response.headers["X-Robots-Tag"] = "index, follow, max-image-preview:large"
        response.add_etag()
        response.make_conditional(request)
        return response
    except Exception:
        app.logger.exception("Dynamic social image rendering failed")
        fallback = Response(base64.b64decode(OG_IMAGE_B64), mimetype="image/png")
        fallback.headers["Cache-Control"] = "public, max-age=3600, stale-while-revalidate=86400"
        fallback.headers["Content-Language"] = path_lang if path_lang in LANGUAGES else "en"
        fallback.headers["Accept-Ranges"] = "bytes"
        fallback.headers["Access-Control-Allow-Origin"] = "*"
        fallback.headers["Cross-Origin-Resource-Policy"] = "cross-origin"
        return fallback


@app.get("/favicon.ico")
def favicon() -> Response:
    return embedded_asset(FAVICON_B64, "image/x-icon", "favicon.ico")


@app.get("/openapi.json")
def openapi_document() -> Response:
    root = site_root()
    language_enum = list(LANGUAGES.keys())
    document = {
        "openapi": "3.1.0",
        "info": {
            "title": f"{APP_NAME} API",
            "version": APP_VERSION,
            "description": "Machine-readable local Panchang timelines calculated with Lahiri ayanamsa and Swiss Ephemeris Moshier.",
        },
        "servers": [{"url": root}],
        "paths": {
            "/api/panchang": {
                "get": {
                    "operationId": "getPanchang",
                    "summary": "Get Panchang for a place, date and local time",
                    "description": "Returns prior, active and at least 12 upcoming intervals for all ten visible Panchang elements.",
                    "parameters": [
                        {"name": "place", "in": "query", "schema": {"type": "string", "default": "Ujjain"}},
                        {"name": "lat", "in": "query", "description": "Latitude; defaults to Ujjain", "schema": {"type": "number", "minimum": -89.8, "maximum": 89.8, "default": 23.1765}},
                        {"name": "lon", "in": "query", "description": "Longitude; defaults to Ujjain", "schema": {"type": "number", "minimum": -180, "maximum": 180, "default": 75.7885}},
                        {"name": "tz", "in": "query", "description": "IANA timezone; defaults to Asia/Kolkata", "schema": {"type": "string", "default": "Asia/Kolkata", "example": "Asia/Kolkata"}},
                        {"name": "date", "in": "query", "schema": {"type": "string", "format": "date"}},
                        {"name": "time", "in": "query", "schema": {"type": "string", "pattern": "^\\d{2}:\\d{2}$", "example": "12:23"}},
                        {"name": "lang", "in": "query", "schema": {"type": "string", "enum": language_enum, "default": "en"}},
                        {"name": "live", "in": "query", "schema": {"type": "boolean", "default": False}},
                    ],
                    "responses": {
                        "200": {
                            "description": "Panchang response",
                            "content": {"application/json": {"schema": {"$ref": "#/components/schemas/PanchangResponse"}}},
                        },
                        "500": {"description": "Calculation error"},
                    },
                }
            },
            "/api/places": {
                "get": {
                    "operationId": "searchPlaces",
                    "summary": "Search places and IANA timezones",
                    "parameters": [
                        {"name": "q", "in": "query", "required": True, "schema": {"type": "string", "minLength": 2}},
                        {"name": "lang", "in": "query", "schema": {"type": "string", "enum": language_enum, "default": "en"}},
                    ],
                    "responses": {"200": {"description": "Matching places"}},
                }
            },
        },
        "components": {
            "schemas": {
                "TimelineItem": {
                    "type": "object",
                    "required": ["title", "time", "current", "quality"],
                    "properties": {
                        "title": {"type": "string"},
                        "time": {"type": "string"},
                        "start": {"type": "string", "format": "date-time"},
                        "end": {"type": "string", "format": "date-time"},
                        "current": {"type": "boolean"},
                        "quality": {"type": "string", "enum": ["auspicious", "inauspicious", "neutral"]},
                        "detail": {"type": "string"},
                    },
                },
                "Section": {
                    "type": "object",
                    "required": ["key", "label", "items"],
                    "properties": {
                        "key": {"type": "string"},
                        "label": {"type": "string"},
                        "icon": {"type": "string"},
                        "items": {"type": "array", "items": {"$ref": "#/components/schemas/TimelineItem"}},
                    },
                },
                "PanchangResponse": {
                    "type": "object",
                    "required": ["query", "headers", "sections", "summary", "generated_at", "method"],
                    "properties": {
                        "query": {"type": "object"},
                        "headers": {"type": "object"},
                        "sections": {"type": "array", "minItems": 10, "maxItems": 10, "items": {"$ref": "#/components/schemas/Section"}},
                        "summary": {"type": "object"},
                        "generated_at": {"type": "string", "format": "date-time"},
                        "method": {"type": "string"},
                    },
                },
            }
        },
    }
    response = jsonify(document)
    response.headers["Access-Control-Allow-Origin"] = "*"
    response.headers["Cache-Control"] = "public, max-age=86400"
    response.headers["Content-Security-Policy"] = "default-src 'none'; frame-ancestors 'none'"
    return response


@app.get("/llms.txt")
def llms_txt() -> Response:
    root = site_root()
    example_date = datetime.now(IST).date().isoformat()
    languages = ", ".join(f"{code} ({meta['name']})" for code, meta in LANGUAGES.items())
    body = f"""# {APP_NAME}

> A live, location-aware Hindu Panchang web application and JSON API.

## Primary pages
- Homepage: {root}/
- Canonical page pattern: {root}/{{language}}/panchang/{{place-slug}}/{{YYYY-MM-DD}}
- Sitemap: {root}/sitemap.xml

## Machine-readable interfaces
- Panchang API: {root}/api/panchang?place=Ujjain&lat=23.1765&lon=75.7885&tz=Asia%2FKolkata&date={example_date}&time=12%3A23&lang=en&live=0
- Place search: {root}/api/places?q=Ujjain&lang=en
- OpenAPI 3.1: {root}/openapi.json

## Data returned
Every Panchang response includes server-rendered and JSON representations of sunrise, sunset, Tithi, Nakshatra, Yoga, Karana, Choghadiya, Hora, special Muhurta/current period, and Lagna. Each timeline includes earlier, active/selected, and at least 12 upcoming values with ISO start/end timestamps where applicable.

## Calculation method
Lahiri ayanamsa; Swiss Ephemeris Moshier planetary positions; local astronomical sunrise/sunset; traditional variable-length Choghadiya and planetary Hora divisions. Timings depend on coordinates, IANA timezone, date and local time. Important religious observances should be verified with a qualified practitioner because regional traditions can differ.

## Supported interface languages
{languages}

## Citation guidance
When quoting data, include the place, coordinates, IANA timezone, local date/time, language, generated_at timestamp and canonical URL or API URL. Prefer the canonical dated page as the human-facing citation.
"""
    response = Response(body, mimetype="text/plain")
    response.headers["Cache-Control"] = "public, max-age=3600"
    response.headers["Access-Control-Allow-Origin"] = "*"
    return response


@app.get("/health")
def health() -> Response:
    response = jsonify({"status": "ok", "app": APP_NAME, "version": APP_VERSION, "time": datetime.now(UTC).isoformat(), "daily_push_configured": push_feature_enabled()})
    response.headers["Cache-Control"] = "no-store"
    response.headers["X-Robots-Tag"] = "noindex, nofollow"
    response.headers["Content-Security-Policy"] = "default-src 'none'; frame-ancestors 'none'"
    return response


if __name__ == "__main__":
    command = sys.argv[1] if len(sys.argv) > 1 else "serve"
    if command == "send-daily-push":
        try:
            print(json.dumps(send_due_push_notifications(), sort_keys=True))
        except Exception as exc:
            app.logger.exception("Daily push job failed")
            print(json.dumps({"error": str(exc)}))
            raise SystemExit(1)
    elif command == "init-push-db":
        ensure_push_table()
        print(json.dumps({"status": "ok", "push_enabled": push_feature_enabled()}))
    else:
        port = int(os.getenv("PORT", "10000"))
        debug = os.getenv("FLASK_DEBUG", "0") in {"1", "true", "True", "yes"}
        app.run(host="0.0.0.0", port=port, debug=debug)
