"""
Panchang — a single-file, mobile-first Flask web application.

Everything required by the app (HTML, CSS, JavaScript, API routes, PWA shell,
SEO metadata and Panchang calculations) lives in this file.  The astronomical
engine is Swiss Ephemeris through pyswisseph, using Lahiri ayanamsa and the
built-in Moshier ephemeris so no separate ephemeris files are required.

Production command (Render):
    gunicorn --bind 0.0.0.0:$PORT panchang:app

License note: pyswisseph is AGPL-3.0. If this application is published as a
network service, review and comply with the Swiss Ephemeris/pyswisseph license.
"""

from __future__ import annotations

import base64
import html
import io
import json
import math
import os
import re
import secrets
import unicodedata
from datetime import date, datetime, time as dt_time, timedelta, timezone
from functools import lru_cache
from typing import Any, Callable, Iterable
from urllib.parse import quote, urlencode
from zoneinfo import ZoneInfo, ZoneInfoNotFoundError

import requests
import swisseph as swe

try:
    from PIL import Image, ImageDraw, ImageFilter, ImageFont
except Exception:  # The static embedded social image remains a safe fallback.
    Image = ImageDraw = ImageFilter = ImageFont = None
from flask import Flask, Response, jsonify, make_response, redirect, request
from jinja2 import BaseLoader, Environment, select_autoescape

try:
    from indic_transliteration import sanscript
    from indic_transliteration.sanscript import transliterate
except Exception:  # The app still works in English if optional transliteration fails.
    sanscript = None
    transliterate = None


app = Flask(__name__)
app.config.update(JSON_SORT_KEYS=False, MAX_CONTENT_LENGTH=32 * 1024)

APP_NAME = os.getenv("PANCHANG_APP_NAME", "Panchang")
APP_VERSION = "1.2.0"
DEFAULT_PLACE = {
    "name": "Ujjain",
    "latitude": 23.1765,
    "longitude": 75.7885,
    "timezone": "Asia/Kolkata",
    "country": "India",
}
TIMELINE_PAST_ITEMS = 4
TIMELINE_FUTURE_ITEMS = 12

UTC = timezone.utc
IST = ZoneInfo("Asia/Kolkata")
ASTRO_FLAGS = swe.FLG_MOSEPH | swe.FLG_SPEED | swe.FLG_SIDEREAL
RISE_SET_FLAGS = swe.FLG_MOSEPH
swe.set_ephe_path("")
swe.set_sid_mode(swe.SIDM_LAHIRI, 0.0, 0.0)


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
    "place": "Place",
    "search_place": "Search city, town or postal code",
    "date": "Date",
    "time": "Time",
    "language": "Language",
    "live_time": "Keep time live",
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
    "geocode_attribution": "Place names: GeoNames/Open-Meteo and OpenStreetMap/Nominatim.",
    "close": "Close",
    "searching": "Searching…",
    "not_available": "Not available",
    "solar_unavailable": "No local sunrise/sunset for this date and latitude",
    "refresh": "Refresh Panchang",
    "refreshing": "Refreshing Panchang…",
    "refreshed": "Panchang refreshed.",
    "auto_refresh": "Automatically refreshes every minute",
    "location_fallback": "Location is unavailable, so Ujjain is being shown.",
    "appearance": "Appearance",
    "light": "Light",
    "dark": "Dark",
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
    "hi": {"appearance": "रूप", "light": "उजला", "dark": "गहरा"},
    "mr": {"appearance": "दृश्यरूप", "light": "उजळ", "dark": "गडद"},
    "gu": {"appearance": "દેખાવ", "light": "ઉજળું", "dark": "ઘેરું"},
    "bn": {"appearance": "রূপ", "light": "হালকা", "dark": "গাঢ়"},
    "ta": {"appearance": "தோற்றம்", "light": "வெளிச்சம்", "dark": "இருள்"},
    "te": {"appearance": "రూపం", "light": "లైట్", "dark": "డార్క్"},
    "kn": {"appearance": "ರೂಪ", "light": "ಬೆಳಕು", "dark": "ಗಾಢ"},
    "ml": {"appearance": "രൂപം", "light": "ലൈറ്റ്", "dark": "ഡാർക്ക്"},
    "pa": {"appearance": "ਦਿੱਖ", "light": "ਹਲਕਾ", "dark": "ਗੂੜ੍ਹਾ"},
    "or": {"appearance": "ଦେଖା", "light": "ଉଜ୍ଜ୍ୱଳ", "dark": "ଗାଢ଼"},
    "ne": {"appearance": "रूप", "light": "उज्यालो", "dark": "गाढा"},
    "sa": {"appearance": "रूपम्", "light": "प्रकाशम्", "dark": "अन्धकारः"},
}
for _language_code, _theme_values in THEME_TEXT.items():
    TEXT_OVERRIDES.setdefault(_language_code, {}).update(_theme_values)

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


def resolve_context(path_lang: str | None = None, place_slug: str | None = None, date_str: str | None = None) -> dict[str, Any]:
    lang = detect_language(path_lang)
    known = POPULAR_PLACES.get(place_slug or "", DEFAULT_PLACE)
    place_name = (request.args.get("place") or known["name"]).strip()[:120]
    latitude = clamp_float(request.args.get("lat"), float(known["latitude"]), -89.8, 89.8)
    longitude = clamp_float(request.args.get("lon"), float(known["longitude"]), -180.0, 180.0)
    tz_name, tz = safe_timezone(request.args.get("tz"), str(known["timezone"]))
    now = datetime.now(tz)
    selected_date = safe_date(date_str or request.args.get("date"), now.date())
    raw_time = request.args.get("time")
    live_requested = request.args.get("live", "1") not in {"0", "false", "False", "no"}
    is_today = selected_date == now.date()
    if raw_time:
        selected_time = safe_time(raw_time, now.timetz().replace(tzinfo=None))
    elif is_today:
        selected_time = now.timetz().replace(tzinfo=None, second=0, microsecond=0)
    else:
        selected_time = dt_time(12, 0)
    selected_at = datetime.combine(selected_date, selected_time, tzinfo=tz)
    # ZoneInfo accepts nonexistent wall times during a DST jump. Round-tripping
    # through UTC moves such a selection to the first real local instant.
    normalized_at = selected_at.astimezone(UTC).astimezone(tz)
    if (normalized_at.date(), normalized_at.hour, normalized_at.minute) != (selected_date, selected_time.hour, selected_time.minute):
        selected_at = normalized_at.replace(second=0, microsecond=0)
        selected_date = selected_at.date()
        selected_time = selected_at.timetz().replace(tzinfo=None)
    live = bool(live_requested and selected_date == now.date() and not raw_time)
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
EN_WEEKDAYS = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday", "Sunday"]


def ordinal(day: int) -> str:
    if 10 <= day % 100 <= 20:
        suffix = "th"
    else:
        suffix = {1: "st", 2: "nd", 3: "rd"}.get(day % 10, "th")
    return f"{day}{suffix}"


def format_clock(value: datetime) -> str:
    hour = value.hour % 12 or 12
    # Keep the meridiem attached to the time when compact cards wrap on mobile.
    return f"{hour}:{value.minute:02d} {'AM' if value.hour < 12 else 'PM'}"


def format_date_label(value: date, lang: str = "en", include_year: bool = True) -> str:
    if lang == "en":
        core = f"{ordinal(value.day)} {EN_MONTHS[value.month - 1]}"
    else:
        core = f"{value.day:02d}-{value.month:02d}"
    return f"{core} {value.year}" if include_year else core


def format_header(value: datetime, place: str, lang: str) -> str:
    return f"{tr(lang, 'panchang')} ({place} - {format_date_label(value.date(), lang)} - {format_clock(value)})"


def format_compact_header(value: datetime, place: str, lang: str) -> str:
    # The mobile header preserves place, date and time while using fewer glyphs
    # so it can stay large enough for older readers on narrow screens.
    date_text = f"{value.day}/{value.month}"
    compact_hour = value.hour % 12 or 12
    compact_clock = f"{compact_hour}:{value.minute:02d}{'a' if value.hour < 12 else 'p'}"
    return f"{tr(lang, 'panchang')} · {place} · {date_text} · {compact_clock}"


def format_point(value: datetime, reference: date) -> str:
    if value.date() == reference:
        return format_clock(value)
    return f"{value.day} {EN_MONTHS[value.month - 1]} · {format_clock(value)}"


def format_range(start: datetime, end: datetime, reference: date) -> str:
    offset_changes = start.utcoffset() != end.utcoffset()
    start_clock = f"{format_clock(start)} {start.tzname() or ''}".strip() if offset_changes else format_clock(start)
    end_clock = f"{format_clock(end)} {end.tzname() or ''}".strip() if offset_changes else format_clock(end)
    if start.date() == end.date() == reference:
        return f"{start_clock} – {end_clock}"
    if start.date() == end.date():
        return f"{start.day} {EN_MONTHS[start.month - 1]} · {start_clock} – {end_clock}"
    return (
        f"{start.day} {EN_MONTHS[start.month - 1]} {start_clock} – "
        f"{end.day} {EN_MONTHS[end.month - 1]} {end_clock}"
    )


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
    return {
        "title": title,
        "time": format_range(start, end, at.date()),
        "start": iso_minute(start),
        "end": iso_minute(end),
        "current": bool(current),
        "quality": quality,
        "detail": detail,
        # The current card is indicated by its border/background; no text badge
        # is rendered so long Panchang names retain the full card width.
        "badge": "",
    }


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
        return {
            "title": title, "time": tr(lang, "solar_unavailable"), "start": "", "end": "",
            "current": focus, "quality": "neutral", "detail": "", "badge": tr(lang, "selected") if focus else "",
        }
    return {
        "title": title,
        "time": format_point(value, at.date()),
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
        weekday = EN_WEEKDAYS[day.weekday()]
        title = f"{day.day} {EN_MONTHS[day.month - 1]} · {weekday}"
        items.append(point_item(title, value, at, lang, offset == 0))
    return items


def make_sun_pair_timeline(at: datetime, latitude: float, longitude: float, tz_name: str, lang: str) -> list[dict[str, Any]]:
    """Return one daily card containing both sunrise and sunset."""
    items: list[dict[str, Any]] = []
    for offset in range(-TIMELINE_PAST_ITEMS, TIMELINE_FUTURE_ITEMS + 1):
        day = at.date() + timedelta(days=offset)
        sunrise, sunset = sun_pair(day, latitude, longitude, tz_name)
        weekday = EN_WEEKDAYS[day.weekday()]
        title = f"{day.day} {EN_MONTHS[day.month - 1]} · {weekday}"
        rise_text = format_clock(sunrise) if sunrise else "—"
        set_text = format_clock(sunset) if sunset else "—"
        unavailable = sunrise is None and sunset is None
        items.append({
            "title": title,
            "time": tr(lang, "solar_unavailable") if unavailable else f"☀ {rise_text}  •  ◒ {set_text}",
            "start": iso_minute(sunrise) if sunrise else "",
            "end": iso_minute(sunset) if sunset else "",
            "current": offset == 0,
            "quality": "neutral",
            "detail": "",
            "badge": "",
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
        title = f"{day.day} {EN_MONTHS[day.month - 1]} · {tr(lang, 'not_available')}"
        items.append({
            "title": title,
            "time": tr(lang, "solar_unavailable"),
            "start": "",
            "end": "",
            "current": offset == 0,
            "quality": "neutral",
            "detail": "",
            "badge": tr(lang, "selected") if offset == 0 else "",
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
    "sun": "☀", "sunrise": "☀", "sunset": "◒", "tithi": "◐", "nakshatra": "✦", "yoga": "∞",
    "karana": "◇", "choghadiya": "◷", "hora": "☉", "period": "ॐ", "lagna": "↟", "reserved": "",
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

    sunrise_items = make_sun_timeline("rise", at, lat, lon, tz_name, lang)
    sunset_items = make_sun_timeline("set", at, lat, lon, tz_name, lang)
    sections = [
        section_model("sun", f"{tr(lang, 'sunrise')} / {tr(lang, 'sunset')}", make_sun_pair_timeline(at, lat, lon, tz_name, lang)),
        section_model("tithi", tr(lang, "tithi"), make_category_timeline("tithi", at, lat, lon, lang)),
        section_model("nakshatra", tr(lang, "nakshatra"), make_category_timeline("nakshatra", at, lat, lon, lang)),
        section_model("yoga", tr(lang, "yoga"), make_category_timeline("yoga", at, lat, lon, lang)),
        section_model("karana", tr(lang, "karana"), make_category_timeline("karana", at, lat, lon, lang)),
        section_model("choghadiya", tr(lang, "choghadiya"), make_choghadiya_timeline(at, lat, lon, tz_name, lang)),
        section_model("hora", tr(lang, "hora"), make_hora_timeline(at, lat, lon, tz_name, lang)),
        section_model("period", tr(lang, "period"), make_period_timeline(at, lat, lon, tz_name, lang)),
        section_model("lagna", tr(lang, "lagna"), make_category_timeline("lagna", at, lat, lon, lang)),
        {"key": "reserved", "label": "", "icon": "", "items": [], "reserved": True},
    ]

    summary = {section["key"]: current_or_focused(section["items"]) for section in sections if section.get("items")}
    summary["sunrise"] = current_or_focused(sunrise_items)
    summary["sunset"] = current_or_focused(sunset_items)
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
            "timezone": tz_name, "date": at.date().isoformat(), "time": at.strftime("%H:%M"),
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
        "languages": [
            {"code": code, "name": info["name"], "native": info["native"]}
            for code, info in LANGUAGES.items()
        ],
        "generated_at": datetime.now(UTC).replace(microsecond=0).isoformat(),
        "method": "Lahiri ayanamsa; Swiss Ephemeris Moshier; local sunrise/sunset; traditional Choghadiya, Hora and Muhurta divisions",
    }


def site_root() -> str:
    configured = os.getenv("SITE_URL", "").strip().rstrip("/")
    if configured:
        return configured
    return request.url_root.rstrip("/")


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
        "tz": context["timezone"], "date": context["date"].isoformat(), "time": context["time"].strftime("%H:%M"),
        "lang": context["lang"], "live": "1" if context["live"] else "0",
    }
    if context.get("country"):
        params["country"] = context["country"]
    return f"{site_root()}/api/panchang?{urlencode(params)}"


def og_image_url(context: dict[str, Any]) -> str:
    params = {
        "place": context["place"], "lat": f"{context['latitude']:.6f}", "lon": f"{context['longitude']:.6f}",
        "tz": context["timezone"], "date": context["date"].isoformat(),
        "time": context["time"].strftime("%H:%M"), "lang": context["lang"], "live": "0",
        "mode": "live" if context.get("live") else "selected", "v": APP_VERSION,
    }
    if context.get("country"):
        params["country"] = context["country"]
    return f"{site_root()}/og.png?{urlencode(params)}"


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
    return {"title": title[:200], "description": description[:320], "canonical": canonical, "alternates": alternates, "og_image": og_image_url(context)}


def build_jsonld(context: dict[str, Any], data: dict[str, Any], seo: dict[str, Any]) -> dict[str, Any]:
    root = site_root()
    place_id = f"{seo['canonical']}#place"
    dataset_id = f"{seo['canonical']}#dataset"
    page_id = f"{seo['canonical']}#webpage"
    app_id = f"{root}#webapp"
    website_id = f"{root}#website"
    publisher_id = f"{root}#publisher"
    social_image = {
        "@type": "ImageObject", "url": seo["og_image"], "contentUrl": seo["og_image"],
        "width": 1200, "height": 630, "caption": seo["title"],
    }
    observations: list[dict[str, Any]] = []
    variables: list[dict[str, Any]] = []
    item_list: list[dict[str, Any]] = []

    for position, section in enumerate(data["sections"], start=1):
        item = current_or_focused(section["items"])
        if not item:
            continue
        variables.append({
            "@type": "PropertyValue",
            "name": section["label"],
            "value": item.get("title", ""),
            "description": item.get("time", ""),
            "propertyID": section["key"],
            "measurementTechnique": data["method"],
        })
        observation = {
            "@type": "Observation",
            "name": f"{section['label']} for {context['place']}",
            "observationAbout": {"@id": place_id},
            "observationDate": context["at"].isoformat(),
            "variableMeasured": section["label"],
            "value": item.get("title", ""),
            "measurementTechnique": data["method"],
            "additionalProperty": [
                {"@type": "PropertyValue", "name": "Display timing", "value": item.get("time", "")},
                {"@type": "PropertyValue", "name": "Classification", "value": item.get("quality", "neutral")},
            ],
        }
        if item.get("start"):
            observation["additionalProperty"].append({"@type": "PropertyValue", "name": "Start", "value": item["start"]})
        if item.get("end"):
            observation["additionalProperty"].append({"@type": "PropertyValue", "name": "End", "value": item["end"]})
        observations.append(observation)
        item_list.append({
            "@type": "ListItem", "position": position,
            "name": section["label"], "description": f"{item.get('title', '')}: {item.get('time', '')}",
        })

    place = {
        "@type": "Place", "@id": place_id, "name": context["place"],
        "geo": {
            "@type": "GeoCoordinates", "latitude": context["latitude"], "longitude": context["longitude"],
        },
        "additionalProperty": {"@type": "PropertyValue", "name": "IANA timezone", "value": context["timezone"]},
    }
    if context.get("country"):
        place["address"] = {"@type": "PostalAddress", "addressLocality": context["place"], "addressCountry": context["country"]}

    graph: list[dict[str, Any]] = [
        {
            "@type": "Organization", "@id": publisher_id, "name": APP_NAME, "url": root,
            "logo": {"@type": "ImageObject", "url": f"{root}/icon-512.png", "width": 512, "height": 512},
        },
        {
            "@type": "WebSite", "@id": website_id, "url": root, "name": APP_NAME,
            "inLanguage": list(LANGUAGES.keys()), "publisher": {"@id": publisher_id},
            "potentialAction": {
                "@type": "SearchAction",
                "target": {"@type": "EntryPoint", "urlTemplate": f"{root}/search?place={{search_term_string}}"},
                "query-input": "required name=search_term_string",
            },
        },
        {
            "@type": "WebApplication", "@id": app_id, "name": APP_NAME, "url": root,
            "applicationCategory": "LifestyleApplication", "applicationSubCategory": "Hindu Panchang and Vedic calendar",
            "operatingSystem": "Any", "browserRequirements": "Requires a modern browser with JavaScript for interactive editing; core Panchang content is server-rendered.",
            "softwareVersion": APP_VERSION, "isAccessibleForFree": True, "image": social_image, "screenshot": seo["og_image"],
            "offers": {"@type": "Offer", "price": "0", "priceCurrency": "USD"},
            "featureList": [
                "Location-aware Panchang", "Tithi timeline", "Nakshatra timeline", "Yoga and Karana timelines",
                "Local sunrise and sunset", "Live Choghadiya and Hora", "Muhurta overlays", "Current Lagna",
                "Multiple Indian languages", "Installable mobile web application",
            ],
            "publisher": {"@id": publisher_id},
        },
        {
            "@type": "WebPage", "@id": page_id, "url": seo["canonical"], "name": seo["title"],
            "headline": seo["title"], "description": seo["description"], "inLanguage": context["lang"],
            "isPartOf": {"@id": website_id}, "about": {"@id": place_id}, "mainEntity": {"@id": dataset_id},
            "dateModified": data["generated_at"], "isAccessibleForFree": True, "primaryImageOfPage": social_image,
            "speakable": {"@type": "SpeakableSpecification", "cssSelector": ["#currentHeaderText", ".metric-row"]},
            "breadcrumb": {"@id": f"{seo['canonical']}#breadcrumb"},
            "potentialAction": [
                {"@type": "ViewAction", "target": seo["canonical"], "name": f"View Panchang for {context['place']}"},
            ],
        },
        {
            "@type": "Dataset", "@id": dataset_id, "name": seo["title"], "description": seo["description"],
            "url": seo["canonical"], "creator": {"@id": app_id}, "publisher": {"@id": publisher_id},
            "dateModified": data["generated_at"], "inLanguage": context["lang"], "isAccessibleForFree": True, "image": social_image,
            "temporalCoverage": context["date"].isoformat(), "spatialCoverage": {"@id": place_id},
            "measurementTechnique": data["method"], "variableMeasured": variables,
            "distribution": {
                "@type": "DataDownload", "contentUrl": api_url(context), "encodingFormat": "application/json",
                "name": "Machine-readable Panchang JSON",
            },
            "keywords": [
                "Panchang", "Panchangam", "Tithi", "Nakshatra", "Yoga", "Karana", "Choghadiya", "Hora",
                "Muhurta", "Lagna", context["place"], context["date"].isoformat(),
            ],
            "hasPart": observations,
        },
        place,
        {
            "@type": "ItemList", "@id": f"{seo['canonical']}#panchang-items", "name": "Current Panchang elements",
            "numberOfItems": len(item_list), "itemListElement": item_list,
        },
        {
            "@type": "BreadcrumbList", "@id": f"{seo['canonical']}#breadcrumb",
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
  --bg-0: #fffdfa;
  --bg-1: #f7f8f5;
  --bg-2: #eef6f3;
  --surface: rgba(255, 255, 255, .92);
  --surface-strong: #ffffff;
  --surface-soft: rgba(255, 255, 255, .72);
  --line: rgba(36, 44, 55, .10);
  --line-strong: rgba(36, 44, 55, .20);
  --text: #171922;
  --muted: #5f6672;
  --gold: #d99712;
  --cyan: #218fa0;
  --mint: #15977f;
  --rose: #d54f74;
  --lavender: #6a63d7;
  --peach: #ef6b55;
  --good: #13876f;
  --good-bg: #dcf6eb;
  --bad: #c84261;
  --bad-bg: #ffe5eb;
  --neutral: #6863c8;
  --header-bg: linear-gradient(112deg, #d6f4ea 0%, #fff1c2 35%, #f9d9e7 69%, #d9f1f4 100%);
  --header-control-bg: rgba(255, 255, 255, .78);
  --shadow: 0 16px 42px rgba(46, 51, 62, .12);
  --shadow-soft: 0 5px 18px rgba(46, 51, 62, .075);
  --radius: clamp(12px, 1.8vmin, 20px);
  --gap: clamp(3px, .48vh, 7px);
  --pad: clamp(5px, .9vmin, 12px);
  --header-height: clamp(58px, 8.4vh, 90px);
  --label-width: clamp(112px, 25vw, 290px);
  --header-left-space: clamp(48px, 6.4vw, 68px);
  --header-right-space: clamp(48px, 6.4vw, 68px);
}

html[data-theme="dark"] {
  color-scheme: dark;
  --bg-0: #101820;
  --bg-1: #16242d;
  --bg-2: #1c3039;
  --surface: rgba(31, 46, 57, .95);
  --surface-strong: #20313c;
  --surface-soft: rgba(35, 52, 64, .90);
  --line: rgba(226, 239, 244, .10);
  --line-strong: rgba(226, 239, 244, .22);
  --text: #f7fbfc;
  --muted: #c1ced4;
  --gold: #f3bd50;
  --cyan: #74d5df;
  --mint: #6ed8b8;
  --rose: #ff8fa3;
  --lavender: #b9b4ff;
  --peach: #ff9f88;
  --good: #70ddb9;
  --good-bg: #173f39;
  --bad: #ff8da0;
  --bad-bg: #4a2b35;
  --neutral: #b9b4ff;
  --header-bg: linear-gradient(112deg, #27463f 0%, #4b4026 35%, #4b2e3d 69%, #203e47 100%);
  --header-control-bg: rgba(13, 25, 33, .68);
  --shadow: 0 18px 52px rgba(0, 0, 0, .33);
  --shadow-soft: 0 7px 20px rgba(0, 0, 0, .22);
}

* { box-sizing: border-box; }
html, body { width: 100%; height: 100%; margin: 0; overflow: hidden; overscroll-behavior: none; }
html { background: var(--bg-0); }
body {
  min-height: 100dvh;
  color: var(--text);
  background:
    radial-gradient(68vmax 43vmax at 0% -13%, rgba(87, 204, 173, .18), transparent 58%),
    radial-gradient(55vmax 42vmax at 102% 1%, rgba(241, 132, 170, .16), transparent 58%),
    radial-gradient(50vmax 35vmax at 78% 112%, rgba(112, 166, 226, .12), transparent 62%),
    linear-gradient(145deg, var(--bg-0), var(--bg-1) 55%, var(--bg-2));
  font-family: Inter, ui-sans-serif, system-ui, -apple-system, BlinkMacSystemFont, "Segoe UI", "Noto Sans",
    "Noto Sans Devanagari", "Noto Sans Bengali", "Noto Sans Tamil", "Noto Sans Telugu", sans-serif;
  -webkit-font-smoothing: antialiased;
  text-rendering: optimizeLegibility;
}
html[data-theme="dark"] body {
  background:
    radial-gradient(68vmax 43vmax at 0% -13%, rgba(87, 204, 173, .10), transparent 58%),
    radial-gradient(55vmax 42vmax at 102% 1%, rgba(241, 132, 170, .09), transparent 58%),
    radial-gradient(50vmax 35vmax at 78% 112%, rgba(112, 166, 226, .08), transparent 62%),
    linear-gradient(145deg, var(--bg-0), var(--bg-1) 55%, var(--bg-2));
}
button, input, select { font: inherit; }
button { -webkit-tap-highlight-color: transparent; }

.ambient { position: fixed; inset: 0; pointer-events: none; overflow: hidden; z-index: 0; }
.ambient::before, .ambient::after { content: ""; position: absolute; border-radius: 50%; opacity: .74; }
.ambient::before {
  width: 38vmax; height: 38vmax; left: -24vmax; top: 18%;
  border: 1px solid rgba(217, 151, 18, .14); box-shadow: 0 0 95px rgba(217, 151, 18, .045) inset;
}
.ambient::after {
  width: 32vmax; height: 32vmax; right: -20vmax; top: 8%;
  border: 1px solid rgba(33, 143, 160, .13); box-shadow: 0 0 90px rgba(33, 143, 160, .045) inset;
}

.app-shell {
  position: relative; z-index: 1; width: 100%; height: 100dvh; max-width: 1920px; margin: 0 auto;
  padding: var(--pad); display: grid; grid-template-rows: var(--header-height) minmax(0, 1fr);
  gap: var(--gap); isolation: isolate;
}

.day-carousel {
  min-width: 0; min-height: 0; overflow: hidden; border: 1px solid rgba(36, 44, 55, .10);
  border-radius: var(--radius); background: var(--header-bg); box-shadow: var(--shadow); position: relative;
}
.day-carousel::before {
  content: ""; position: absolute; inset: 0; pointer-events: none;
  background:
    radial-gradient(32% 145% at 0% 50%, rgba(255, 255, 255, .36), transparent 72%),
    radial-gradient(30% 145% at 100% 50%, rgba(255, 255, 255, .30), transparent 72%);
}
html[data-theme="dark"] .day-carousel { border-color: var(--line); }
html[data-theme="dark"] .day-carousel::before { opacity: .14; }
.day-rail {
  position: relative; z-index: 1; display: flex; width: 100%; height: 100%; overflow-x: auto; overflow-y: hidden;
  scroll-snap-type: x mandatory; scrollbar-width: none; overscroll-behavior-x: contain; touch-action: pan-x;
}
.day-rail::-webkit-scrollbar, .timeline::-webkit-scrollbar { display: none; }
.day-panel {
  flex: 0 0 100%; width: 100%; min-width: 0; height: 100%; scroll-snap-align: center; scroll-snap-stop: always;
  display: grid; place-items: center; padding: 0 calc(var(--header-right-space) + 8px) 0 calc(var(--header-left-space) + 8px);
}
.day-title {
  display: block; width: 100%; margin: 0; white-space: nowrap; text-align: center; overflow: hidden;
  color: var(--text); font-size: clamp(18px, 2.55vw, 42px); line-height: 1; font-weight: 900; letter-spacing: -.04em;
  font-variant-numeric: tabular-nums;
}
.header-compact { display: none; }
.day-panel[data-position="previous"] .day-title,
.day-panel[data-position="next"] .day-title { opacity: .76; }

.header-control {
  min-width: 44px; min-height: 44px; border: 1px solid rgba(36, 44, 55, .13); border-radius: 999px;
  display: grid; place-items: center; color: var(--text); background: var(--header-control-bg); cursor: pointer;
  box-shadow: 0 7px 20px rgba(51, 55, 66, .12), inset 0 1px 0 rgba(255,255,255,.48);
  transition: transform .16s ease, background .16s ease, border-color .16s ease, box-shadow .16s ease, opacity .16s ease;
  backdrop-filter: blur(8px);
}
html[data-theme="dark"] .header-control { box-shadow: 0 8px 24px rgba(0,0,0,.24), inset 0 1px 0 rgba(255,255,255,.05); }
.header-control:hover { transform: translateY(-1px); border-color: rgba(33,143,160,.36); filter: brightness(1.02); }
.header-control:active { transform: translateY(1px) scale(.97); }
.header-control:disabled { opacity: .55; cursor: wait; }
.previous-control {
  position: absolute; z-index: 5; left: clamp(6px, .8vw, 12px); top: 50%; transform: translateY(-50%);
  width: clamp(40px, 5.2vmin, 52px); height: clamp(40px, 5.2vmin, 52px); color: #8a5b00;
  border-color: rgba(217,151,18,.25); background: rgba(255, 248, 223, .78); font-size: clamp(27px, 3.3vmin, 38px); line-height: 1;
}
.previous-control:hover { transform: translateY(-51%); border-color: rgba(217,151,18,.48); }
.previous-control:active { transform: translateY(-49%) scale(.97); }
.header-actions {
  position: absolute; z-index: 6; right: clamp(6px, .8vw, 12px); top: 50%; transform: translateY(-50%);
  display: flex; align-items: center;
}
.header-actions .header-control { position: relative; width: clamp(40px, 5.2vmin, 52px); height: clamp(40px, 5.2vmin, 52px); }
.next-control {
  color: #8a5b00; border-color: rgba(217,151,18,.25); background: rgba(255, 248, 223, .78);
  font-size: clamp(27px, 3.3vmin, 38px); line-height: 1;
}
html[data-theme="dark"] .previous-control,
html[data-theme="dark"] .next-control { color: #ffe3a1; background: rgba(83, 66, 30, .54); }
.next-control:hover { border-color: rgba(217,151,18,.48); }
.live-dot {
  position: absolute; z-index: 4; left: calc(var(--header-left-space) + 10px); bottom: clamp(5px, .65vh, 9px);
  display: inline-flex; align-items: center; gap: 6px; color: var(--mint); font-size: clamp(8px, 1.05vh, 11px);
  font-weight: 950; letter-spacing: .13em; text-transform: uppercase; pointer-events: none;
}
.live-dot::before { content: ""; width: 7px; height: 7px; border-radius: 50%; background: currentColor; box-shadow: 0 0 0 4px rgba(21,151,127,.14); animation: pulse 2s infinite; }
.live-dot[hidden] { display: none; }
@keyframes pulse { 50% { opacity: .5; box-shadow: 0 0 0 9px rgba(21,151,127,0); } }

.metrics {
  min-width: 0; min-height: 0; display: grid; grid-template-rows: repeat(10, minmax(0, 1fr)); gap: var(--gap);
  transition: opacity .16s ease, transform .16s ease, filter .16s ease;
}
.metrics.is-busy { filter: saturate(.88) brightness(.98); }
.metric-row {
  --row-accent: #218fa0;
  min-width: 0; min-height: 0; display: grid; grid-template-columns: var(--label-width) minmax(0, 1fr);
  align-items: stretch; gap: var(--gap); border: 0; border-radius: var(--radius); background: transparent;
  overflow: visible;
}
.metric-row[data-section="sun"] { --row-accent: #d6930d; }
.metric-row[data-section="tithi"] { --row-accent: #168f79; }
.metric-row[data-section="nakshatra"] { --row-accent: #d85282; }
.metric-row[data-section="yoga"] { --row-accent: #7a66dc; }
.metric-row[data-section="karana"] { --row-accent: #e26955; }
.metric-row[data-section="choghadiya"] { --row-accent: #cc7b20; }
.metric-row[data-section="hora"] { --row-accent: #258da4; }
.metric-row[data-section="period"] { --row-accent: #6c64d8; }
.metric-row[data-section="lagna"] { --row-accent: #4a76c8; }
.metric-label {
  min-width: 0; display: flex; align-items: center; gap: clamp(7px, 1vw, 14px); padding: 0 clamp(9px, 1.3vw, 18px);
  background: color-mix(in srgb, var(--row-accent) 15%, var(--surface-strong));
  border: 0; border-radius: var(--radius) 7px 7px var(--radius); position: relative; box-shadow: var(--shadow-soft);
}
.metric-label::after { display: none; }
.metric-icon {
  flex: 0 0 auto; width: clamp(25px, 3.55vh, 37px); aspect-ratio: 1; display: grid; place-items: center;
  border-radius: 50%; color: var(--row-accent); background: color-mix(in srgb, var(--row-accent) 10%, var(--surface-strong));
  border: 1px solid color-mix(in srgb, var(--row-accent) 28%, transparent);
  font-size: clamp(13px, 2.2vh, 21px); line-height: 1;
}
.metric-label h2 {
  min-width: 0; margin: 0; color: var(--text); font-size: clamp(12.5px, 2.05vh, 20px); line-height: 1.08;
  font-weight: 880; letter-spacing: -.022em; overflow-wrap: normal; word-break: normal; hyphens: none; text-wrap: balance;
}
.timeline-wrap {
  min-width: 0; min-height: 0; position: relative; overflow: hidden; border-radius: 7px var(--radius) var(--radius) 7px;
  background: color-mix(in srgb, var(--row-accent) 4%, var(--surface)); box-shadow: var(--shadow-soft);
}
.timeline-wrap::before, .timeline-wrap::after { display: none; }
.timeline {
  width: 100%; height: 100%; min-width: 0; display: flex; align-items: stretch; gap: var(--gap);
  overflow-x: auto; overflow-y: hidden; padding: clamp(3px, .45vh, 6px) clamp(13px, 2vw, 30px) clamp(3px, .45vh, 6px) 0;
  scroll-padding-left: 0; scroll-snap-type: x mandatory; scrollbar-width: none; overscroll-behavior-x: contain;
  touch-action: pan-x; -webkit-overflow-scrolling: touch; cursor: grab;
}
.timeline:active { cursor: grabbing; }
.moment {
  --quality-color: transparent;
  --quality-bg: color-mix(in srgb, var(--row-accent) 6%, var(--surface-strong));
  flex: 0 0 clamp(244px, 37vw, 520px); min-width: 0; height: 100%; scroll-snap-align: start; scroll-snap-stop: normal;
  display: grid; grid-template-columns: minmax(0, 1fr) auto; grid-template-rows: 1fr 1fr; align-items: center;
  column-gap: clamp(8px, 1vw, 14px); padding: 0 clamp(12px, 1.45vw, 19px); border-radius: calc(var(--radius) - 4px);
  border: 2px solid transparent; background: var(--quality-bg); color: var(--text); box-shadow: 0 1px 3px rgba(39,44,54,.06);
  transition: transform .16s ease, border-color .16s ease, background .16s ease, box-shadow .16s ease;
  position: relative; contain: layout paint; font-variant-numeric: tabular-nums;
}
html[data-theme="dark"] .moment { box-shadow: 0 2px 7px rgba(0,0,0,.13); }
.moment::before { display: none; }
.moment.neutral { --quality-bg: color-mix(in srgb, var(--row-accent) 6%, var(--surface-strong)); }
.moment.auspicious { --quality-color: var(--good); --quality-bg: var(--good-bg); }
.moment.inauspicious { --quality-color: var(--bad); --quality-bg: var(--bad-bg); }
.moment.auspicious::before,
.moment.inauspicious::before {
  content: ""; display: block; position: absolute; left: 0; top: 15%; bottom: 15%; width: 4px;
  border-radius: 0 999px 999px 0; background: var(--quality-color);
}
.moment:hover { filter: brightness(1.015); }
.moment.is-current {
  transform: translateZ(0); border-color: transparent;
  background: color-mix(in srgb, var(--row-accent) 11%, var(--surface-strong));
  box-shadow: 0 7px 18px rgba(42,48,59,.10);
}
.moment.neutral.is-current::before {
  content: ""; display: block; position: absolute; left: 0; top: 15%; bottom: 15%; width: 4px;
  border-radius: 0 999px 999px 0; background: var(--row-accent);
}
.moment.auspicious.is-current { border-color: var(--good); background: var(--good-bg); box-shadow: 0 0 0 2px rgba(19,135,111,.10), 0 7px 18px rgba(42,48,59,.10); }
.moment.inauspicious.is-current { border-color: var(--bad); background: var(--bad-bg); box-shadow: 0 0 0 2px rgba(200,66,97,.10), 0 7px 18px rgba(42,48,59,.10); }
.moment.is-current::after { display: none; }
.moment-title {
  grid-column: 1; grid-row: 1; align-self: end; min-width: 0; padding-bottom: 2px;
  white-space: nowrap; overflow: hidden; text-overflow: ellipsis; font-size: clamp(14px, 2.1vh, 20px);
  line-height: 1.04; font-weight: 890; letter-spacing: -.018em;
}
.moment-time {
  grid-column: 1 / -1; grid-row: 2; align-self: start; min-width: 0; padding-top: 2px;
  white-space: nowrap; overflow: hidden; text-overflow: ellipsis; color: var(--muted);
  font-size: clamp(12px, 1.68vh, 16px); line-height: 1.08; font-weight: 690;
}
.badges {
  grid-column: 2; grid-row: 1; display: flex; flex-direction: row; align-items: flex-end; justify-content: flex-end;
  align-self: end; gap: clamp(2px, .34vh, 4px); min-width: 0; padding-bottom: 2px;
}
.badges:empty { display: none; }
.badge {
  max-width: clamp(78px, 18vw, 126px); padding: clamp(2px, .35vh, 4px) clamp(6px, .72vw, 10px);
  border-radius: 999px; white-space: nowrap; overflow: hidden; text-overflow: ellipsis;
  font-size: clamp(7.5px, 1.16vh, 11px); line-height: 1.05; font-weight: 950; letter-spacing: .055em;
  text-transform: uppercase; border: 0;
}
.badge.good { color: #0e5f4e; background: #bcebdc; }
.badge.bad { color: #873049; background: #ffc8d3; }
.badge.neutral { color: #4f489e; background: #dedbff; }
html[data-theme="dark"] .badge.good { color: #e9fff7; background: rgba(33,143,111,.52); }
html[data-theme="dark"] .badge.bad { color: #fff0f3; background: rgba(180,58,83,.55); }
html[data-theme="dark"] .badge.neutral { color: #f2f0ff; background: rgba(105,96,203,.50); }

.reserved-row { pointer-events: none; }
.reserved-row .reserved-label,
.reserved-row .reserved-space {
  min-width: 0; min-height: 0; border-radius: var(--radius);
  background: rgba(255,255,255,.30); box-shadow: inset 0 0 0 1px rgba(36,44,55,.035);
}
html[data-theme="dark"] .reserved-row .reserved-label,
html[data-theme="dark"] .reserved-row .reserved-space { background: rgba(255,255,255,.025); box-shadow: inset 0 0 0 1px rgba(255,255,255,.025); }

.fab {
  position: fixed; z-index: 20; right: max(12px, calc((100vw - 1920px) / 2 + 16px)); bottom: max(12px, env(safe-area-inset-bottom));
  width: clamp(52px, 7.2vmin, 68px); aspect-ratio: 1; border: 1px solid rgba(182, 102, 31, .20); border-radius: 50%;
  display: grid; place-items: center; color: #381d0e; cursor: pointer;
  background: linear-gradient(145deg, #fff2b7, #ffc46e 48%, #ff9a82);
  box-shadow: 0 14px 34px rgba(95, 63, 36, .22), 0 0 0 5px rgba(255, 190, 111, .16);
  transition: transform .17s ease, box-shadow .17s ease, filter .17s ease;
}
html[data-theme="dark"] .fab { color: #32190d; box-shadow: 0 14px 36px rgba(0,0,0,.40), 0 0 0 5px rgba(244,189,79,.10); }
.fab svg { width: 43%; height: 43%; fill: none; stroke: currentColor; stroke-width: 2.25; stroke-linecap: round; stroke-linejoin: round; }
.fab:hover { transform: translateY(-2px) rotate(-3deg); filter: brightness(1.02); }
.fab:active { transform: translateY(1px) scale(.97); }
.fab::after {
  content: attr(data-tooltip); position: absolute; right: calc(100% + 10px); top: 50%; transform: translateY(-50%) translateX(4px);
  opacity: 0; pointer-events: none; white-space: nowrap; padding: 8px 11px; border-radius: 10px;
  color: var(--text); background: var(--surface-strong); border: 1px solid var(--line-strong); font-size: 13px; font-weight: 750;
  box-shadow: var(--shadow-soft); transition: opacity .15s ease, transform .15s ease;
}
.fab:hover::after, .fab:focus-visible::after { opacity: 1; transform: translateY(-50%) translateX(0); }

.settings-sheet {
  width: min(94vw, 650px); max-height: min(94dvh, 820px); margin: auto; padding: 0; border: 1px solid var(--line-strong);
  border-radius: clamp(20px, 4vw, 32px); color: var(--text); background: var(--surface-strong);
  box-shadow: 0 30px 90px rgba(54,55,64,.24); overflow: hidden;
}
html[data-theme="dark"] .settings-sheet { box-shadow: 0 35px 100px rgba(0,0,0,.64); }
.settings-sheet::backdrop { background: rgba(25, 28, 35, .46); backdrop-filter: blur(8px) saturate(.90); }
html[data-theme="dark"] .settings-sheet::backdrop { background: rgba(1,8,14,.72); }
.settings-form { max-height: min(94dvh, 820px); display: grid; grid-template-rows: auto minmax(0,1fr) auto; }
.sheet-head {
  display: flex; align-items: center; justify-content: space-between; gap: 16px; padding: clamp(16px, 3vw, 25px);
  border-bottom: 1px solid var(--line); background: linear-gradient(110deg, #dff7ef, #fff2c7 45%, #f9dce7);
}
html[data-theme="dark"] .sheet-head { background: linear-gradient(110deg, #223f39, #433b25 45%, #422d38); }
.sheet-head h2 { margin: 0; font-size: clamp(22px, 3.7vw, 30px); letter-spacing: -.025em; }
.icon-button {
  width: 44px; aspect-ratio: 1; border-radius: 50%; border: 1px solid var(--line); background: var(--surface-soft);
  color: var(--text); cursor: pointer; display: grid; place-items: center; font-size: 24px;
}
.icon-button:hover { filter: brightness(.98); }
.sheet-body { min-height: 0; overflow-y: auto; overscroll-behavior: contain; padding: clamp(15px, 3vw, 25px); display: grid; gap: 16px; }
.field { display: grid; gap: 8px; min-width: 0; }
.field > label, .field-label { color: var(--text); font-size: 14px; font-weight: 900; letter-spacing: .045em; text-transform: uppercase; }
.input-shell { position: relative; min-width: 0; }
.input-shell input, .field input, .field select {
  width: 100%; min-width: 0; height: 52px; border: 1px solid var(--line-strong); border-radius: 14px;
  color: var(--text); background: color-mix(in srgb, var(--cyan) 3%, var(--surface-strong)); padding: 0 14px; outline: none; font-size: 17px;
  transition: border-color .15s ease, box-shadow .15s ease, background .15s ease;
}
.field select {
  appearance: none;
  background-image: linear-gradient(45deg, transparent 50%, var(--muted) 50%), linear-gradient(135deg, var(--muted) 50%, transparent 50%);
  background-position: calc(100% - 19px) 22px, calc(100% - 13px) 22px; background-size: 6px 6px; background-repeat: no-repeat; padding-right: 40px;
}
.input-shell input:focus, .field input:focus, .field select:focus { border-color: rgba(33,143,160,.70); box-shadow: 0 0 0 4px rgba(33,143,160,.12); background: var(--surface-strong); }
.field input:disabled { opacity: .52; cursor: not-allowed; }
.place-results { display: grid; gap: 6px; margin-top: 8px; max-height: 220px; overflow-y: auto; border-radius: 13px; }
.place-result {
  width: 100%; min-height: 50px; display: grid; grid-template-columns: minmax(0,1fr) auto; align-items: center; gap: 10px; text-align: left; cursor: pointer;
  color: var(--text); background: color-mix(in srgb, var(--cyan) 4%, var(--surface-strong)); border: 1px solid var(--line); border-radius: 12px; padding: 10px 12px;
}
.place-result:hover, .place-result:focus-visible { border-color: rgba(33,143,160,.45); background: color-mix(in srgb, var(--cyan) 10%, var(--surface-strong)); }
.place-main { min-width: 0; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; font-size: 15px; font-weight: 800; }
.place-sub { color: var(--muted); font-size: 12px; white-space: nowrap; }
.form-grid { display: grid; grid-template-columns: repeat(2, minmax(0,1fr)); gap: 13px; }
.switch-row { display: flex; align-items: center; justify-content: space-between; gap: 14px; min-height: 48px; padding: 0 2px; }
.switch-row > label:first-child { font-size: 16px; font-weight: 780; color: var(--text); }
.switch { position: relative; width: 54px; height: 30px; flex: 0 0 auto; }
.switch input { position: absolute; opacity: 0; pointer-events: none; }
.switch-track { position: absolute; inset: 0; border-radius: 999px; background: rgba(95,102,114,.17); border: 1px solid var(--line-strong); transition: .18s ease; cursor: pointer; }
.switch-track::after { content: ""; position: absolute; width: 22px; height: 22px; left: 3px; top: 3px; border-radius: 50%; background: var(--surface-strong); box-shadow: 0 2px 8px rgba(0,0,0,.18); transition: .18s ease; }
.switch input:checked + .switch-track { background: rgba(21,151,127,.24); border-color: rgba(21,151,127,.50); }
.switch input:checked + .switch-track::after { transform: translateX(24px); background: var(--mint); }
.switch input:focus-visible + .switch-track { box-shadow: 0 0 0 4px rgba(33,143,160,.14); }
.theme-field { border: 0; margin: 0; padding: 0; }
.theme-toggle { display: grid; grid-template-columns: 1fr 1fr; gap: 8px; padding: 5px; border-radius: 15px; background: color-mix(in srgb, var(--lavender) 6%, var(--surface-strong)); border: 1px solid var(--line); }
.theme-choice {
  min-height: 46px; border: 0; border-radius: 11px; color: var(--muted); background: transparent; cursor: pointer;
  display: inline-flex; align-items: center; justify-content: center; gap: 9px; font-size: 16px; font-weight: 850;
}
.theme-choice svg { width: 20px; height: 20px; fill: none; stroke: currentColor; stroke-width: 2; stroke-linecap: round; stroke-linejoin: round; }
.theme-choice[aria-pressed="true"] { color: var(--text); background: var(--surface-strong); box-shadow: 0 4px 13px rgba(47,49,58,.10); }
html[data-theme="dark"] .theme-choice[aria-pressed="true"] { box-shadow: 0 5px 15px rgba(0,0,0,.22); }
.location-button {
  min-height: 50px; border: 1px solid rgba(33,143,160,.28); border-radius: 14px; color: #126575;
  background: #e4f6f7; cursor: pointer; font-size: 16px; font-weight: 820;
}
html[data-theme="dark"] .location-button { color: #e7fbfd; background: rgba(33,143,160,.16); }
.location-button:hover { filter: brightness(.98); border-color: rgba(33,143,160,.48); }
.sheet-note { margin: 0; color: var(--muted); font-size: 13px; line-height: 1.48; }
.sheet-actions {
  display: grid; grid-template-columns: 1fr 1.55fr; gap: 11px; padding: clamp(14px, 3vw, 23px);
  border-top: 1px solid var(--line); background: color-mix(in srgb, var(--gold) 3%, var(--surface-strong));
}
.action-button { min-height: 52px; border-radius: 15px; border: 1px solid var(--line-strong); cursor: pointer; font-size: 16px; font-weight: 880; }
.action-button.secondary { color: var(--text); background: var(--surface-soft); }
.action-button.primary { color: #321d0b; background: linear-gradient(135deg, #fff0ad, #ffc966 58%, #f8a56f); border-color: rgba(202,139,25,.30); box-shadow: 0 8px 22px rgba(190,124,27,.14); }
.action-button:hover { filter: brightness(1.02); }

.toast {
  position: fixed; z-index: 50; left: 50%; bottom: max(17px, env(safe-area-inset-bottom)); transform: translate(-50%, 18px);
  max-width: min(90vw, 560px); padding: 11px 15px; border-radius: 13px; color: var(--text);
  background: var(--surface-strong); border: 1px solid var(--line-strong); box-shadow: 0 13px 38px rgba(47,49,58,.18);
  font-size: 14px; font-weight: 760; opacity: 0; pointer-events: none; transition: opacity .18s ease, transform .18s ease;
}
.toast.show { opacity: 1; transform: translate(-50%, 0); }
.loading-mask {
  position: fixed; z-index: 40; inset: 0; display: grid; place-items: center; pointer-events: none; opacity: 0;
  background: rgba(246, 244, 239, .36); transition: opacity .12s ease;
}
html[data-theme="dark"] .loading-mask { background: rgba(3,12,20,.24); }
.loading-mask.show { opacity: 1; }
.spinner { width: 40px; aspect-ratio: 1; border-radius: 50%; border: 3px solid rgba(95,102,114,.16); border-top-color: var(--gold); animation: spin .7s linear infinite; }
@keyframes spin { to { transform: rotate(360deg); } }

:focus-visible { outline: 3px solid var(--cyan); outline-offset: 3px; }

@media (min-width: 900px) {
  :root { --label-width: clamp(220px, 20vw, 310px); }
  .moment { flex-basis: clamp(340px, 30vw, 560px); }
}

@media (max-width: 560px) {
  :root {
    --label-width: clamp(108px, 30vw, 130px);
    --header-left-space: 44px;
    --header-right-space: 44px;
    --header-height: clamp(54px, 7.8vh, 70px);
  }
  .header-full { display: none; }
  .header-compact { display: inline; }
  .day-panel { padding-left: calc(var(--header-left-space) + 3px); padding-right: calc(var(--header-right-space) + 3px); }
  .day-title { font-size: clamp(15px, 4.65vw, 21px); letter-spacing: -.035em; }
  .previous-control { left: 5px; width: 42px; height: 42px; min-width: 42px; min-height: 42px; }
  .header-actions { right: 5px; }
  .header-actions .header-control { width: 42px; height: 42px; min-width: 42px; min-height: 42px; }
  .live-dot { display: none; }
  .metric-label { gap: 6px; padding-inline: 7px; }
  .metric-icon { width: clamp(22px, 3.25vh, 29px); font-size: clamp(12px, 1.9vh, 16px); }
  .metric-label h2 { font-size: clamp(12.8px, 1.90vh, 16px); line-height: 1.04; }
  .timeline { padding-right: 22px; }
  .moment { flex-basis: calc(100vw - var(--label-width) - 15px); min-width: 198px; max-width: 360px; padding-inline: 10px; column-gap: 5px; }
  .moment-title { font-size: clamp(14.3px, 2.02vh, 18px); }
  .moment-time { font-size: clamp(12.2px, 1.73vh, 15px); }
  .badge { max-width: 83px; }
  .badges { gap: 1px; }
  .fab { width: 54px; right: 9px; bottom: max(9px, env(safe-area-inset-bottom)); }
  .fab::after { display: none; }
  .form-grid { grid-template-columns: 1fr; }
}

@media (max-width: 560px) and (min-height: 650px) {
  .moment-time {
    white-space: normal; text-overflow: clip; display: -webkit-box; -webkit-box-orient: vertical; -webkit-line-clamp: 2;
    line-height: 1.03; overflow: hidden;
  }
}

@media (max-width: 360px) {
  :root { --label-width: 108px; --header-left-space: 40px; --header-right-space: 40px; }
  .metric-label { padding-inline: 5px; gap: 5px; }
  .metric-icon { width: 21px; }
  .metric-label h2 { font-size: 12.6px; line-height: 1.01; }
  .moment { min-width: 188px; padding-inline: 8px; }
  .badge { padding-inline: 5px; max-width: 76px; }
  .fab { width: 48px; }
}

@media (max-height: 640px) {
  :root { --gap: 2px; --pad: 4px; --radius: 10px; --header-height: 47px; }
  .day-title { font-size: clamp(13px, 2.55vw, 25px); }
  .previous-control, .header-actions .header-control { width: 38px; height: 38px; min-width: 38px; min-height: 38px; }
  .live-dot { display: none; }
  .metric-label { padding-inline: 6px; gap: 5px; }
  .metric-icon { width: 20px; font-size: 10px; }
  .metric-label h2 { font-size: clamp(12px, 2.25vh, 13.2px); line-height: 1.01; }
  .timeline { padding-block: 2px; }
  .moment { padding-inline: 8px; column-gap: 6px; }
  .moment-title { font-size: clamp(13.5px, 2.55vh, 14.8px); }
  .moment-time { font-size: clamp(11.5px, 2.15vh, 12.8px); }
  .badge { font-size: clamp(7px, 1.45vh, 8px); padding: 2px 4px; max-width: 72px; }
  .fab { width: 44px; }
}

@media (orientation: landscape) and (max-height: 480px) {
  :root { --label-width: clamp(126px, 19vw, 198px); --header-height: 41px; --header-left-space: 36px; --header-right-space: 36px; }
  .day-title { font-size: clamp(12px, 2.1vw, 20px); }
  .previous-control, .header-actions .header-control { width: 30px; height: 30px; min-width: 30px; min-height: 30px; font-size: 23px; }
  .moment { flex-basis: clamp(280px, 39vw, 430px); grid-template-rows: 1fr; grid-template-columns: minmax(0,1.2fr) minmax(0,.95fr) auto; padding-inline: 8px; column-gap: 6px; }
  .metric-label h2 { font-size: 10.8px; }
  .moment-title { grid-column: 1; grid-row: 1; align-self: center; padding: 0; font-size: 11.2px; }
  .moment-time { grid-column: 2; grid-row: 1; align-self: center; padding: 0; text-align: right; font-size: 9.7px; }
  .badges { grid-column: 3; grid-row: 1; margin-left: 2px; gap: 1px; }
  .badge { font-size: 6.5px; padding: 1px 4px; }
  .fab { width: 36px; right: 6px; bottom: 6px; }
}

@media (prefers-reduced-motion: reduce) {
  *, *::before, *::after { animation-duration: .001ms !important; animation-iteration-count: 1 !important; scroll-behavior: auto !important; transition-duration: .001ms !important; }
}

@media (forced-colors: active) {
  .moment, .metric-label, .timeline-wrap, .day-carousel, .fab, .header-control { border: 1px solid CanvasText; }
  .badge { border: 1px solid CanvasText; }
}
"""

JS = r"""
(() => {
  'use strict';

  const initialNode = document.getElementById('initial-data');
  let state = JSON.parse(initialNode.textContent);
  let settings = {
    place: state.query.place,
    slug: state.query.slug,
    lat: state.query.lat,
    lon: state.query.lon,
    timezone: state.query.timezone,
    date: state.query.date,
    time: state.query.time,
    language: state.query.language,
    live: Boolean(state.query.live),
    country: state.query.country || '',
    locationMode: 'server'
  };
  let loading = false;
  let selectedPlace = true;
  let placeMatches = [];
  let dayScrollTimer = 0;
  let suppressDayScroll = true;
  let searchTimer = 0;
  let toastTimer = 0;
  let lastDataFetch = Date.now();
  let lastLiveMinute = '';

  const $ = (selector, root = document) => root.querySelector(selector);
  const $$ = (selector, root = document) => Array.from(root.querySelectorAll(selector));
  const metrics = $('#metrics');
  const dayRail = $('#dayRail');
  const dialog = $('#settingsDialog');
  const form = $('#settingsForm');
  const placeInput = $('#placeInput');
  const placeResults = $('#placeResults');
  const dateInput = $('#dateInput');
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
  const themeColorMeta = $('#themeColor');
  const themeButtons = $$('[data-theme-choice]');
  let activeTheme = document.documentElement.dataset.theme === 'dark' ? 'dark' : 'light';

  const cssEscape = window.CSS && typeof window.CSS.escape === 'function'
    ? window.CSS.escape.bind(window.CSS)
    : value => String(value).replace(/[^a-zA-Z0-9_-]/g, char => `\${char}`);

  const localeMap = {
    en: 'en-IN', hi: 'hi-IN', mr: 'mr-IN', gu: 'gu-IN', bn: 'bn-IN', ta: 'ta-IN',
    te: 'te-IN', kn: 'kn-IN', ml: 'ml-IN', pa: 'pa-IN', or: 'or-IN', ne: 'ne-NP', sa: 'sa-IN'
  };

  function applyTheme(theme, persist = true) {
    activeTheme = theme === 'dark' ? 'dark' : 'light';
    document.documentElement.dataset.theme = activeTheme;
    themeButtons.forEach(button => button.setAttribute('aria-pressed', String(button.dataset.themeChoice === activeTheme)));
    if (themeColorMeta) themeColorMeta.content = activeTheme === 'dark' ? '#16242d' : '#f6f2ea';
    if (persist) {
      try { localStorage.setItem('panchang-theme', activeTheme); } catch (_) { /* Storage is optional. */ }
    }
  }

  applyTheme(activeTheme, false);

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

  function qualityBadge(item) {
    if (item.quality === 'auspicious') return `<span class="badge good">${escapeHtml(state.ui.good)}</span>`;
    if (item.quality === 'inauspicious') return `<span class="badge bad">${escapeHtml(state.ui.avoid)}</span>`;
    return '';
  }

  function renderMoment(item) {
    const badges = [];
    const qBadge = qualityBadge(item);
    if (qBadge) badges.push(qBadge);
    if (item.detail && item.detail === state.ui.mixed) badges.push(`<span class="badge neutral">${escapeHtml(item.detail)}</span>`);
    const classes = ['moment', item.quality || 'neutral', item.current ? 'is-current' : ''].filter(Boolean).join(' ');
    const currentAttr = item.current ? ' aria-current="true"' : '';
    const datetimeAttr = item.start ? ` datetime="${escapeHtml(item.start)}"` : '';
    const aria = `${item.title}. ${item.time}. ${item.current ? (item.badge || state.ui.selected) : ''}`;
    return `
      <article class="${classes}" role="listitem"${currentAttr} aria-label="${escapeHtml(aria)}">
        <strong class="moment-title" itemprop="value">${escapeHtml(item.title)}</strong>
        <time class="moment-time"${datetimeAttr}>${escapeHtml(item.time)}</time>
        <span class="badges">${badges.join('')}</span>
      </article>`;
  }

  function alignedCurrentScrollLeft(rail, current) {
    const leftPadding = parseFloat(getComputedStyle(rail).paddingLeft) || 0;
    return Math.max(0, current.offsetLeft - leftPadding);
  }

  function captureTimelineState() {
    const snapshot = {};
    $$('.metric-row', metrics).forEach(row => {
      const rail = $('.timeline', row);
      if (!rail) return;
      const current = $('.moment.is-current', rail);
      const target = current ? alignedCurrentScrollLeft(rail, current) : Number.NaN;
      snapshot[row.dataset.section] = {
        scrollLeft: rail.scrollLeft,
        nearCurrent: Number.isFinite(target) && Math.abs(rail.scrollLeft - target) <= Math.max(34, current.offsetWidth * .18)
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
        rail.scrollLeft = alignedCurrentScrollLeft(rail, current);
      } else {
        rail.scrollLeft = Math.min(saved.scrollLeft, Math.max(0, rail.scrollWidth - rail.clientWidth));
      }
    });
  }

  function renderSections(timelineState = null) {
    metrics.innerHTML = state.sections.map(section => {
      if (section.reserved) {
        return `<section class="metric-row reserved-row" data-section="reserved" aria-hidden="true"><div class="reserved-label"></div><div class="reserved-space"></div></section>`;
      }
      return `
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
        </section>`;
    }).join('');
    bindTimelineInteractions();
    requestAnimationFrame(() => timelineState ? restoreTimelineState(timelineState) : alignCurrentItems());
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

  function alignCurrentItems() {
    $$('.timeline', metrics).forEach(rail => {
      const current = $('.moment.is-current', rail);
      if (!current) return;
      rail.scrollLeft = alignedCurrentScrollLeft(rail, current);
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
      dayRail.scrollLeft = dayRail.clientWidth;
      fitHeaderText();
      window.setTimeout(() => { suppressDayScroll = false; }, 90);
    });
    liveIndicator.hidden = !settings.live;
  }

  function fitHeaderText() {
    $$('.day-title', dayRail).forEach(node => {
      node.style.fontSize = '';
      const maximum = parseFloat(getComputedStyle(node).fontSize) || 24;
      let low = window.innerWidth <= 560 ? 12 : 14;
      let high = maximum;
      for (let i = 0; i < 8; i += 1) {
        const mid = (low + high) / 2;
        node.style.fontSize = `${mid}px`;
        if (node.scrollWidth <= node.clientWidth) low = mid;
        else high = mid;
      }
      node.style.fontSize = `${Math.max(window.innerWidth <= 560 ? 12 : 14, low - .15)}px`;
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
    previousDayButton.setAttribute('aria-label', state.ui.previous_day);
    nextDayButton.setAttribute('aria-label', state.ui.next_day);
    liveIndicator.textContent = state.ui.live;
    applyTheme(activeTheme, false);
  }

  function renderSeo() {
    if (!state.seo) return;
    document.title = state.seo.title;
    const description = $('meta[name="description"]');
    if (description) description.content = state.seo.description;
    const canonical = $('link[rel="canonical"]');
    if (canonical) canonical.href = state.seo.canonical;
    const ogTitle = $('meta[property="og:title"]');
    const ogDescription = $('meta[property="og:description"]');
    const ogUrl = $('meta[property="og:url"]');
    const ogImage = $('meta[property="og:image"]');
    const ogSecureImage = $('meta[property="og:image:secure_url"]');
    const ogImageAlt = $('meta[property="og:image:alt"]');
    const twitterTitle = $('meta[name="twitter:title"]');
    const twitterDescription = $('meta[name="twitter:description"]');
    const twitterImage = $('meta[name="twitter:image"]');
    const twitterImageAlt = $('meta[name="twitter:image:alt"]');
    if (ogTitle) ogTitle.content = state.seo.title;
    if (ogDescription) ogDescription.content = state.seo.description;
    if (ogUrl) ogUrl.content = state.seo.canonical;
    if (ogImage) ogImage.content = state.seo.og_image;
    if (ogSecureImage) ogSecureImage.content = state.seo.og_image;
    if (ogImageAlt) ogImageAlt.content = state.seo.title;
    if (twitterTitle) twitterTitle.content = state.seo.title;
    if (twitterDescription) twitterDescription.content = state.seo.description;
    if (twitterImage) twitterImage.content = state.seo.og_image;
    if (twitterImageAlt) twitterImageAlt.content = state.seo.title;
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
      date: settings.date,
      time: settings.time,
      lang: settings.language,
      live: settings.live ? '1' : '0'
    });
    if (settings.country) params.set('country', settings.country);
    return `/api/panchang?${params.toString()}`;
  }

  function animationDone(animation) {
    return animation ? animation.finished.catch(() => undefined) : Promise.resolve();
  }

  async function fetchPanchang(direction = 0, historyMode = 'push', {timelineState = null, showMask = true} = {}) {
    if (loading) return false;
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
        live: Boolean(state.query.live),
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
      savePreferences();
      updateHistory(historyMode);
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
    if (settings.live) {
      params.delete('time');
      params.set('live', '1');
    } else {
      params.set('time', settings.time);
      params.set('live', '0');
    }
    const localUrl = `${target.pathname}${params.toString() ? `?${params.toString()}` : ''}`;
    const method = mode === 'replace' ? 'replaceState' : 'pushState';
    history[method]({panchang: true}, '', localUrl);
  }

  async function shiftDay(direction) {
    if (loading || ![-1, 1].includes(direction)) return;
    settings.date = addDays(settings.date, direction);
    settings.live = false;
    await fetchPanchang(direction, 'push');
  }

  async function refreshNow({preserveScroll = true} = {}) {
    if (loading) return false;
    const timelineState = preserveScroll ? captureTimelineState() : null;
    if (settings.live) applyCurrentZonedTime();
    return fetchPanchang(0, 'replace', {timelineState, showMask: false});
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
    requestAnimationFrame(() => {
      placeInput.focus();
      selectPlaceText();
    });
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
    applyTheme(activeTheme, false);
    toggleLiveFields();
    placeResults.innerHTML = '';
    selectedPlace = true;
  }

  function toggleLiveFields() {
    dateInput.disabled = liveInput.checked;
    timeInput.disabled = liveInput.checked;
  }

  function selectPlaceText() {
    if (!placeInput.value) return;
    try { placeInput.select(); } catch (_) { /* Selection is best-effort on mobile browsers. */ }
  }

  editButton.addEventListener('click', openDialog);
  closeButton.addEventListener('click', closeDialog);
  cancelButton.addEventListener('click', closeDialog);
  themeButtons.forEach(button => button.addEventListener('click', () => applyTheme(button.dataset.themeChoice)));
  placeInput.addEventListener('focus', () => requestAnimationFrame(selectPlaceText));
  placeInput.addEventListener('click', selectPlaceText);
  liveInput.addEventListener('change', toggleLiveFields);
  languageInput.addEventListener('change', () => { settings.language = languageInput.value; });
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
  }

  placeInput.addEventListener('input', () => {
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

  function applyCurrentZonedTime() {
    const parts = getZonedParts(settings.timezone);
    settings.date = `${parts.year}-${String(parts.month).padStart(2, '0')}-${String(parts.day).padStart(2, '0')}`;
    settings.time = `${String(parts.hour).padStart(2, '0')}:${String(parts.minute).padStart(2, '0')}`;
  }

  async function reverseDevicePlace(latitude, longitude) {
    try {
      const params = new URLSearchParams({lat: String(latitude), lon: String(longitude), lang: settings.language});
      const response = await fetch(`/api/reverse-place?${params.toString()}`, {headers: {'Accept': 'application/json'}, cache: 'force-cache'});
      if (!response.ok) throw new Error(`HTTP ${response.status}`);
      const payload = await response.json();
      if (payload.place?.name) return payload.place;
    } catch (error) {
      console.warn('City name could not be resolved.', error);
    }
    const coordinateName = `${Number(latitude).toFixed(3)}, ${Number(longitude).toFixed(3)}`;
    return {name: coordinateName, display_name: coordinateName, country: '', slug: ''};
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
      const resolvedPlace = await reverseDevicePlace(settings.lat, settings.lon);
      settings.place = resolvedPlace.name;
      settings.country = resolvedPlace.country || '';
      settings.slug = resolvedPlace.slug || '';
      settings.live = true;
      settings.locationMode = 'auto';
      selectedPlace = true;
      applyCurrentZonedTime();
      placeInput.value = resolvedPlace.display_name || resolvedPlace.name;
      liveInput.checked = true;
      toggleLiveFields();
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
    settings.live = liveInput.checked;
    if (selectedPlace && settings.locationMode !== 'auto') settings.locationMode = 'manual';
    if (settings.live) {
      applyCurrentZonedTime();
    } else {
      settings.date = dateInput.value || settings.date;
      settings.time = timeInput.value || settings.time;
    }
    closeDialog();
    await fetchPanchang(0, 'push');
  });

  function savePreferences() {
    try {
      localStorage.setItem('panchang-preferences-v3', JSON.stringify({
        place: settings.place, lat: settings.lat, lon: settings.lon, timezone: settings.timezone,
        country: settings.country, language: settings.language, slug: settings.slug || '',
        locationMode: settings.locationMode || 'manual'
      }));
    } catch (_) { /* Storage is optional. */ }
  }

  function loadPreferences() {
    try {
      const raw = localStorage.getItem('panchang-preferences-v3') || localStorage.getItem('panchang-preferences-v2');
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
    const dateValue = new Date(Date.UTC(parts.year, parts.month - 1, parts.day + offset, 12));
    const locale = localeMap[settings.language] || 'en-IN';
    let dateText;
    let compactDate;
    if (settings.language === 'en') {
      const day = dateValue.getUTCDate();
      const remainder = day % 100;
      const suffix = remainder >= 11 && remainder <= 13 ? 'th' : ({1: 'st', 2: 'nd', 3: 'rd'}[day % 10] || 'th');
      const month = new Intl.DateTimeFormat(locale, {month: 'short', timeZone: 'UTC'}).format(dateValue);
      dateText = `${day}${suffix} ${month} ${dateValue.getUTCFullYear()}`;
      compactDate = `${day}/${dateValue.getUTCMonth() + 1}`;
    } else {
      dateText = new Intl.DateTimeFormat(locale, {day: 'numeric', month: 'short', year: 'numeric', timeZone: 'UTC'}).format(dateValue);
      compactDate = `${dateValue.getUTCDate()}/${dateValue.getUTCMonth() + 1}`;
    }
    const timeText = new Intl.DateTimeFormat(locale, {
      hour: 'numeric', minute: '2-digit', hour12: true, timeZone: settings.timezone
    }).format(new Date());
    const compactHour = parts.hour % 12 || 12;
    const compactTime = `${compactHour}:${String(parts.minute).padStart(2, '0')}${parts.hour < 12 ? 'a' : 'p'}`;
    return {
      full: `${state.ui.panchang} (${settings.place} - ${dateText} - ${timeText})`,
      compact: `${state.ui.panchang} · ${settings.place} · ${compactDate} · ${compactTime}`
    };
  }

  function liveTick() {
    if (!settings.live || loading) return;
    const parts = getZonedParts(settings.timezone);
    const minuteKey = `${parts.year}-${parts.month}-${parts.day}-${parts.hour}-${parts.minute}`;
    if (minuteKey === lastLiveMinute) return;
    lastLiveMinute = minuteKey;
    applyCurrentZonedTime();
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
    fitHeaderText();
  }

  async function minuteRefresh() {
    if (document.visibilityState !== 'visible' || loading) return;
    await refreshNow({preserveScroll: true});
  }

  function scheduleMinuteRefresh() {
    const firstDelay = 60000 - (Date.now() % 60000) + 900;
    window.setTimeout(() => {
      minuteRefresh();
      window.setInterval(minuteRefresh, 60000);
    }, firstDelay);
  }

  window.addEventListener('resize', () => {
    fitHeaderText();
    alignCurrentItems();
    suppressDayScroll = true;
    dayRail.scrollLeft = dayRail.clientWidth;
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
      timezone: fallback.timezone, country: fallback.country || 'India', language, live: true, locationMode: 'default'
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
      settings = {...settings, ...saved, language: savedLanguage, live: true, locationMode: 'manual'};
      applyCurrentZonedTime();
      await fetchPanchang(0, 'replace', {showMask: false});
      return;
    }

    if (await mayRequestGeolocation()) {
      const located = await useDeviceLocation({auto: true, fetchImmediately: true});
      if (located) return;
    }

    const alreadyUjjain = settings.place === (state.default_location?.name || 'Ujjain')
      && Math.abs(Number(settings.lat) - Number(state.default_location?.lat || 23.1765)) < .001
      && settings.language === savedLanguage;
    applyUjjainFallback(savedLanguage);
    if (!alreadyUjjain) await fetchPanchang(0, 'replace', {showMask: false});
  }

  if ('serviceWorker' in navigator && location.protocol === 'https:') {
    window.addEventListener('load', () => navigator.serviceWorker.register('/sw.js').catch(() => undefined));
  }

  document.addEventListener('visibilitychange', () => {
    if (document.visibilityState === 'visible' && Date.now() - lastDataFetch >= 60000) minuteRefresh();
  });

  renderAll();
  window.setInterval(liveTick, 15000);
  liveTick();
  scheduleMinuteRefresh();
  personalizeInitialView();
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

OG_IMAGE_B64 = (
    "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"
    "e7fv2P33suWHDhmhdtJzQrojJKEsFqzyoKZqW5LAKt2omdrEQBexwI5HSksD3Bb7PseG60Vpnfun0df2T6+sMtpk0lbBO0XRlPmH"
    "aVet0al/7NeIV2xYqdTR++knHr391psNPCjIktFAAemD994aPWqk4a717D/oyJFAUyLsThJmFUZ17dypVauWrVq0aNWyRaOGDcLC"
    "wsyotLS0dM/efWvW/rtw0eK1/67z2spo2EQTa9b8a/ZvdVNStF9SVlb20bRPX3vzHa/fh4WFXTp86I3XT+zauZPD4Qh5n5ycnLnz"
    "F3762Ze79uzlMwJhjLt06jiwf59+fXq1b9dWi5C+bd/+A2v+Wbfmn3WLly3PycnVeFWfXj1++uZzvc/asXPX4Euv8KfnITfr0HPu"
    "nPkLPvnsKxZ6jo+Pu6hzp9atWrZu2bw1JTvfvXff6rXr5i9avPaf9cX+tuwas/OFf/5aNyVZl51/MO1/L7/5rq/+Rw4fcsv1Ey/q"
    "3FGL/rNzcufMXzjdnP5DOnhSndrXXj124tVj0+pq8uU9e/d/8+Ov3/34qy/9/v2HL3t2v0iXeNt27Bpy2biSUrGGIa9IQH8cp32K"
    "hfrndrB+MDYsIVZMgd6EEFurBlaEEAd6jq0IYfqXXYd9n0iLNQlFCAWjhRhZEQSlJoQG1MWOEPrGobopKSuWLgwPDzfWu5tum7xo"
    "8RK/D0mIj+928UVDB/bo2KlLkybNMWYVXLOysn/+dcbX3/5w6PBhk8NMn149fzBEVIZcernnby4bOeLx/3uoXlqqbmsh5M+58559"
    "8ZXMzJPsBp46dWpfc9WYa666okH9+rRQKC4uXrp85cw//1qwaPH5vDw+hPCykcOfNKrn2XPnPfviqydM6zkhIb77xV17dru4R7eL"
    "WrdswdTOf/hlxlff/Zh+6IjJW/Xt1ePnbz/Te9X2nbsHVtX/6JHDn/6/B43pf9bc+c8Y1X8QB4+Pi73/zkm3XD8hMjJSt4azc977"
    "6JNPPv/azeWqxcQc2L7OgIRd+gw5cjRDQB7IcC5O+1waIIRGHowNS6hymT2Hu4u6NgcSQfvt2wkMa0T3TW+3b3q79C+7IoTmTTjj"
    "yZQUO/Pdq0fzJ5xBOo9SpDGewJpkKRsOGgaPHT++ZOlywzevX6+e34eMv/qqzetWf/rxB2OvmtC0KcNZMkIoPj7u9ltvWr543huv"
    "vlinTm1rpxEpycnfffXZ1PffNjBLRghhjEddOnzZwrlDLxnEAvCkpDovPPvk2mULH33oPopsECEUHh5+yaABH77z+sa1y1q1aM5B"
    "zz989b9pJvR82aXDly+cM8y4nhFCaOLVY7etW/X5xx/ceuN1bVq1ZG3nd9x20+rFf7396gtJdWpbG8vrJif99NWnn7z/lmH9j750"
    "2MqFfw67ZCBFFQ3u33fVwjl33naTATboIpPPPvHw/Fk/t2zeTP3QL4Rk0KzVKLYJFg75uxgIKnCk8jbyt7rOqnFfPSro2zsXG5w/"
    "4cz8CWcOfdmVPS2UzN4wbB3UOUCsWrPW+LwwJcXvQ3p0u9jYEkTjEd/huGbc2GV/z7ti9CirdN6j+8V/zf6tX59eJu9To3r1z6Z9"
    "eNvNN1Ic151hYXdOumX1kvk333Ctsemyxla9WrX27dow1XPP7hfPn/0rFT1/Pu2D22++wYwk/O18wtVjVi2eO+bykawigoZeL5z9"
    "W38a+v9y2geTTOjfk2E++9jD338+rXatRJO3atu65dzfv6fLVIFt2Yd7iKNRAoTcHTaFm8MR8wiDL5W3lkOGehGhksLCP8ccs0Pf"
    "SwoLSwrL6/gP/T7RrzZsSwVtzgaNDbkHDx40/MSYajFC2UD1atU+eOeNl194lvM0HSE0buwVP3zzRa3ERDpQYjzlqceunzieytSv"
    "aZPGc2f++uSjD0dFRckeAK8ee8WP33xOUc/PPfXYDSH0LFyrXq3aR++8/uoLz4SwcwaT8GvGXvHLN5/VSqxJS//PP/XojROvMXOT"
    "iPDwT95/667bb6bVx2oxMV9Of//6CeOU4QZATxXkgUDIORBC8Bnx2aD787DvEz0JkvLNvXHRt9dUOSFQQfnYoGHdncvKMk4Io6MF"
    "7NP1E8e//frLTNfvebWJ48e99drLTnMVRHzbC1Oe6tK5o8lxfdiQQXP++LlN65YKBMBrx497+7WXqOv5xSlPdvXWswRx8sZrr3n3"
    "jZe87ZzlxO+68ePefe1F6vp/SY/+vUKrw+H46O3XRl86jK5IGOPXX3xm3JjRMHNUiZ7KOsRj8zzQ1s0hvAUx9BmFK8p40R6vBaL7"
    "PAq9KN+aTNrq1X0anFDE2DF15kGE0J2XNwnEBm09VJgeXcwQJyJqX8deefkD997F51mtW7V89cXnWPBPZ1jYB2+/ERERYXiwuOmG"
    "if/7+IPq1aopEPFat2r52otTGOn5w7dfj4iIkG6ONe7K0Q/deycfodq0avHGi88y0v/Ut1/TrP8qwf+lZ56gzgbdnPDV558SPHqL"
    "MkIRyhNaOHOCBgmEJBMNQkh4gGzLmag5KuhJeNzbBZtSrfApsgL3+6O7XtsmTSwflS98CJgYFNqEAsSehPh4w7e8cKFA2O7ef8+d"
    "vXp056RaZtnIBvXrTb7tFmNA33TDxBeffYpnplRqPd9x280yzrEevPeO3j27KaD/O2+7SXvYd/0be/moW66fYC96AGLZHGgCWPAl"
    "hAyZvonZIrEV//Nhg14sKNA3bZIk9DrownSqEKigomxQwzy2ceNGhm+fnyfu6fAOh+Ol559xOp2yO/ukW26MiYnWgTVCCKERQy95"
    "4ZknYSqgvU32o2cJ5lgOh+PV558Ol9/O7whq524SWBm4GjZ486UptuAGGMRCADRgYRkhJDRBhkaNDfqtI9qU8TGAIrT9oYiub6pQ"
    "j5UCFVSLDWqKPeVf6tWjh+HnHDt+XGRradqk8cRrxsnu+/HxcePGXKFrPtC0SeN33nhFpdwgHz1fPeYKGedYTZs0nnjNVQro/5qq"
    "du6ZDPT9/usvPhMdHaWgIUIy0G480JZY8JwvOaxGGMswbZSACnqxQS1XKZ8kbBKYAOtZPirlGlG1oxsFSDTzQNcPqal1+/frY/hp"
    "h48cEdxmbrnpegV40dgrRmufD4SFhX307ptq7Bu0WM/ytNtuuk4BO7/qisuCk0B3mB09cnifnt3VsTxIBtqNBEIyUC5CSIxABY0m"
    "GwxEdXybV5JQMU64X093NCwfNW6r8DaDulq4hPmAD3ny0UfMLKrctWev4NA0btSwT68eshtYp47t69ZN1mgoN99wbdvWrcArDbTO"
    "HdvXTUmWUfImjRr2ld/ONerf4XA8ct9dInekRrI2K4JkoN14IK8rYarm2ZxcEDYxf2Tma2rYgYHEYNNJW3nywCa81ql6sUEtz3Vp"
    "zK3DlkOGVugQQrwoHscFiRAPuf+eu0ZeOtzw3U9kZh49mqH3qrKyshPHjx1KP7hlx969+/anHzp8/vz58+fz8vLyzuflFRUVRUZG"
    "REZG1qhRIzkpqW5Kcvt2bbt07tS5UwfDCZBhQy9ZvnK17GbWu2ePn3/7PeTX4uPjHr7/HvBKw61Prx4//fq7+fuUlZUdOZqxd/+B"
    "vfsO7N23/0D6YZeZnz+fdz4v323nsTVqpCTVqVs3pX271hd17tTFhJ0PHzp4mfx23qdX959+/SP4d0YNH9KsSSPBOxKXmpadcdSq"
    "0K9/wIK5Ae1B37hGAQshCaE/4oYRs1tTuA9WwZgMsEHftm96O717C8Xn0rpY6K4F8z044TDDmpQsLmOrBRCbBLpa7dq1pjz9xKhL"
    "R5h50pq1/2r/ck5OzrLlK/9esmzfjrXZWVkIofRM/8eHXrhQcOFCQVZW9pEjRxFCM2fPQQjVq5d2x+23XjvhagPT5UsGDXji6ed4"
    "WsWJE5l/zJ6zYOHioxkZp8+cTUiIb9mi+VVjLh89coTh6X73i7tqIYQ3X38tlcWi23fsWvPPv2v+XZeefvhcdva5c1kOB46Pi4+P"
    "j0tJTurUoX2XTh06d+wQG1vDQvc/cSLz99lz5lXouWZCfMsWzceNufxyc3o2QwhzcnKXLF+5aMmyxUtXnD13rjJQEH92XlCQlZ19"
    "+OhRtAH9PnsOQqh+vbS7br/l+gnjDMg/dNCAx55+nqf+j5/I/H323HkL/z6Sccyl/1Ytml89ZrQZ/fe4uGtIQnjDhKtNSr523YbZ"
    "c+avWrvu5KnTObm5tRJrptZNGdS/z+Wjhjdu2IA+JxR3UkZDMtozJ7mzGsADVSWEouEUjEViRezJDBvknCTk0Pab686uBfNbDhnm"
    "VqySnNBCNyWCyuWnhYWFxdaokVgrsWP7dr179Rw5YpiBU7+82uw5c0OriJCly1d89uXXq1auKSktRQg1TIp0/alhUmQgTujbjhw5"
    "+sTTUzZu2vzOm6/qlTMlObluSgqf+jelpaX/++LrN95+v6Cg8kCOzMyTmZknly1f+cuvv0/78J0aNYyQqFYtW4T8TlRU1E3XTzTZ"
    "hcVLl7/34bT1GzcRP1z9xPETJ3bu2r146XKEkDMsrFfP7lddOXrUiGHh4eE87bm0tPTTL75+/e33L3jo+UTmyROZJ5cuX/nTr79/"
    "8uE7sYb03LplcyOhgJAly1Z++uU3K1eV23nVv2qNCIePHH306ec2bNr8/puv6LfzpLopyceOn+Cj/0+++PrVtz8o8NH/kuUrf/z1"
    "j08/fJuR/uulpfbsfpEZEvvo0y/MX7TE65fHT2Su37j5rfemTrrlhsceusd8eHQBHZcWIE9oq5FS+QYk0AaEECOmqztp3RqrY1hU"
    "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"
    "paXFXNmr9o2XpLgs7Z1Jza56aRsjffZuE+eX+z1wZb01O3PmbzgrEvGo/LD7aP63i0+u2JaVnlmQk19aPTqsVb2YMb1q3zgk2aW0"
    "9yY3HfPidt+7vHxjo2bJ4a7Pa/YWTF2UtSm9sKCYpNV0Xta52h2D4+vEh1/WPTGkOdw3OhUhtGJ79oezM/7dnZudV1I7LnzERYlT"
    "JjZw2eFT1zT4dnFmIDvcfTT/m8UnV27POphZkJNXKf9NFfK/G0B+wbCQsjlp3cgkJ+S1Ck9osu61k5A6FWTNCf2Rw3Vo1UWVf+i1"
    "Lq9XR4YaNMcGPTXsq/z909oihBpP3uYFWdAHiU8FecUvYrEeaPFTLe3j2Uee/Wqfexp9/GzhF/Mzth7MnfNyZwfGteMjerdLWLI5"
    "0HyCycHxBKHbRgQsGHDbpancCCFC6O1fD00clFItKqxFWrVx/ZJ+XKp13nzsTOHNb26ftaYKYcs6X7J2Z/bandkzVpz847kOEeGO"
    "QZ1qNqkbs/9Y6JVF0ZFhnz3YekjXRIRQdl7Jta9uW7Mjy9f+Ojer4fow9vkt2w9V1gg5lVV0Kqtox6G8BetDaG/q7KPPfrWfkHKT"
    "O3628PP5x7YcPP/Xy50cGNWOj+jTLmGxj0kcO1N405s7AvX3txUn/3iuQ2R5f6OD72DU2H5ZfvKuD3YF2qhz7EzhjW8ElmflyZlB"
    "5KF3VsTtgS150qWpC7jM1AuLy2asPHXT0JTUWpH92icsqdgNG+HEY/vUQQidyi5eqEESuiHoo1lHn/rqgGfk+WzesS0Hzs9/paMD"
    "ozrxEX3bxf+9+ZzpISUglj8vPzn5gz1mNnrhcksruuHNnTOrLs7MOl+ydmfO2p05v604Neu5dpHhjsGdEprWjd5X1dJoqXTyiIBL"
    "OSZfWtc8IaS+1/bYmcLr39j1h4/S1uzMWbMz55eVp/58rm0gpTWtG33twPIXGV8tOnHvx+XjV1xq6r7M4rf/yvp7x4Wf70muFlme"
    "vouMjQ3i1B/Mznjyq4NuOzx2tuh/84//d/D8opc7ODCqEx/er138Ih87zDhTeN2bVeUnVeSf81zbyHDHJf7kBxJIpdFcMkoMxRWz"
    "JcSwoSgm0sIzv+VkAm0XNM8G3ZzQi0Sxar3WVf5j2iixwUpVT/aj6gPT2h6Y1lYDiNYvEA0RqLilybUvEOVYdovd2RJbDuRO+Wq/"
    "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"
    "MBIo3FjSt3//MKfzZGbmgr/+uvbGGwcMHmySEEr1btIbi2cef8L3Kw0aNUIIZRw9unrVKr19pwI2IeTM6dN/L1x4MjPzxVdfjYiI"
    "6NOv3++//qoWG7Q+IDRo1BAhdFQD0LLyO5jsStZF3YI+/vhToGwdzyYKGg2xoQNjhDyWjAqZ7HedjU75tQTbNaK0r2C6QJRZYhBj"
    "3qfMm2KDmGViEDPoNL/F24QFhiIfHK+/DRw8GCG0avly1x6wtHr1mrVoofRQhPUhhlBkZCRCKD8/X2Pf2YG9dcuW8+fPI4TS0tKU"
    "YIMC+IWHCBqBlqnx3cEidGTQb2vWpQdVWJ1rZR9oPrv8XrZchCm8TVX9hVNAEujX8dmV5zd9d+vXiEIRUebXG6GCjAyWbVUnCxkE"
    "585SafUbNGjStBlCaOXy5ZknTuzds6dZ8+YDBw/eu3u33lul1qs3bvz4du3bx8bFZWdnb1y37ofvvjtz+rTvN1u3bTti5MhWrVvH"
    "JyQUFRUdPnRo+dKl8+fOLSkp8fxaTEzMRd26de/Zs36DBrVq10YInczM3LB+/czffjt37pzXPX/6/feoqKg3nn348MF9nr+vk5T0"
    "6ZdfIoSuGn15UVFR/4EDH3jkYdef7r7vvrvvu8/1OePo0Ttvux1h9PzLL5cXlZk9GyF0xZgxN95yi+s7zVu0mDl3ruvzay+/vHrl"
    "SoTQTzNmREVFPXTffXv37sVez/3iC4TQVZdfXlRUxIChkSoqql+/iopmzPBV0bsfftioceM3X3tt144d48aP79ylS3xCQl5e3rYt"
    "W77/9lu/hWpat2kzbMQIF1KFBQUnTpz4959/Fsybf+7sWd8v165Te9z48V08b/vNt0eq3jYmJubibt279+xRv0GDWrVrVQi84Y/f"
    "vAV+76MPGzVu9Marr+3auXPc+Gs8brvV97auFhUdPWbsmN59+9RJSiq4ULBv397Zf8zav2/fV99/ixAaP3ZcXl4eCeCXV4y58uYK"
    "oFu0aDF77hzX51dffmXVypUIIYfDMWjw4AEDBzZs1DA6OjonO2fHjh2z/vhj586dXrd6/8MPGzVu9MZrr+3bu++qq8e179ChZs2a"
    "p06duv2WW31lTkhI+PyrL51O5wP33rdv3z7fHn3z7TdR0dHPPv30xg0bXSHOJcnAqpLM9CfJrzN+i4qKeuDe+/fu3ev5+6SkpM++"
    "/BwhdOXoK93G+cFHHzRq3Oj1V1/ft2/fuHHj2nds7xL7tptvC2KH7qsOHjh49fir27dvHxsXm52dvX7d+h++++G0P/f3ajExMd26"
    "XdyjZ48GFSaRmXlyw/r1M3773deGEUJt2rQefumI1q1bJSQkFBYUHj9x4t9//pk/b8FZH5ts07bNyJGXtmrdOiEhvqio6PChw0uX"
    "Lv3rr3lecSa4VPXrN6hdIdX69etnzPAj1YcfftC4caPXXnt9x46d48df06VLl4SE+Ly8vC1btn777Xe+thoZGTl2zJi+/fomJydd"
    "uFCwb9++mX/M3LfvgJZRY+DAAQ8/8qDr83333XPfffe4Ph89mnH7bZMJQq/4Kyrz0UfvN27c6NVX39i3b/+ECVd36NAhLi723Lms"
    "NWvWfPvtD7m5uRjjIUMGDx06pH79ek6n88CBgz/88NO6det9BWjbts3IkSNaV2j10KHDS5cumzu3XKvYwvHawGBLZB24bUYCtYLj"
    "FFZmX8PDLG4NVBCooGhUEHFdIwok0IzuBgwajBA6cfz4/n37XLSwWfPmffr1+2z6dC3Tpkrm0K7dPQ8+GBER4foxMTHxkmHDuvfs"
    "+fTjjx88cKBSNRjfcvvtoy6/vDKCO50tW7Vq2apVvwEDpjz5pGdy5sZbbhk6YoQXfa3foMHAQYOeeuyxw4cOaX6hyAM3Pqi3a9++"
    "evXqCKGMjAyE0I033xxQRY8/7ldFLVq2vPOee2JiYlw/xsXF9erTp1OXLv/34INHDh/2ROr2O+4YMXKk+zcRERE1YmObNW/eokWL"
    "55+d4nXbli1b3nWvn9s+8oD7ttiF6bARw/0JPPDJx57wFdjfbXt36tL5kQce8pQWIRQbG/vSa680aNjQ9WN4eHinzp07de488/c/"
    "Ku3dKEhR0dFPP/N0+w4d3L+pmVizd5/evfv0/ubrr3/+8Sd/vKXtfQ884PYIB/ZfAO/cuXNrVq/u07fvsBHDP3z/A6+/9h/QPyo6"
    "+vjx45s2bnLFOpckHQJI8pM/SXRZa5u2be5/8P6QYnuThHZtPa9KTEwcOmxoz549n3j8iYMHDgaP0jffctPwqibRoEH9Bg3qDxw0"
    "8InHnjh0qIpN3nHn5EtHXlrVJms0b96sRYsWU559rvKbDnzb7beNHn1Z1TjTsmWrlv0H9H/6qWdCJoFvvtm/VIMGDXz88SpSedrq"
    "Pffc7Wmrffr0/v/2zjy+yuL6/3PCTYQCQlhEgbAvYV9UxFohQbQiWlBAQRbFrSAuLaht3dpaW/u1y/enaLVWq7Uu2CqIyiLIIphQ"
    "tdpWBERAVgnCNwgpEgji+f1xk8vN3fLcZ5nnnJnzvHj1RTG5c+Z8zpmZ9z3zzJx++sCZM2/bERerjRo1euCBX3bu3DkWqAMHDhg4"
    "cMC8efODHj169eo5c+atMZlatmzxve9d0r9//1tvnTlr1g++851zYj/Zo0fhz39+7y9/+euSktJaY8IN140eXcurPXoU9uhRWFxc"
    "dPdd94ZQWtf1Nhaj8qCxlzw50DpCzeY6darzlxrA1yElQ8jkpD+0wXlbQLNrln6PhcFFB9ihBSqlVE5OTtGwYUqpd2ouDChZterq"
    "a69t1LjxmYMHr3nnHedajBg5sry8/MnHH//XBx+gUv0HDLh+2rQWLVv+6K67bpk+PVaFGHvFFZeMHn3kyJH5c+euWrly3969DRs1"
    "6te//+SpU7sXFk676abfP/hg7JMPHTq0ZPHiktWr9+zevX///kaNG3cvLLxy8uR27dv/4LbbZt58sws5Vi5fvnL58l//7rc9evZ8"
    "5KGHlr75ZubezXvllXmvvHL+d7970623frpx4+0//GH2oOlHVAI0a9as/8CBV02dqpQ6duxYVLITLiorO+GiSZPatW//g1mzZt5y"
    "S/JHXTJqVNnu3Q//7/9+smFD1dGjffr1mzZjRn5+/tXXXPOLn53AvCsnTYrS4MoVK96Y/9r2bdsikchprU87a/DZTZvlp/jY0aPK"
    "du9+6PfVH9u3X79pN83Iz8+feu218fR46NChNxcvLln9zp7dUYMbdS8snDh5Urv27X9426wf3nxL+o/9pOro0b79+tZ87DUJUDrj"
    "lpvbd+hw9OjRp598qmT1O5WVlR07dZp63TWjLh3thAbnvTJ33itzL/jud2++9ZaNGzfe9sOZ8f91+o3T+/brd/z48Reef375W8sO"
    "HjzYtqDt5ClTzhw0aPKUKbt27iyNWzdHn4suHlm2e/dTTz718dq1mW8RWPjGgnOHDBlaVPTnJ59KWFJfeOEIpdTiRYuwZs/ujTdO"
    "71djybI4SwYNGjR5ypSd8ZagmwFq5MUjy3aXPfXkU2s/Wuv88oOLRl5UXl7+xONPfPjBh6hwwIAB35/2/RYtW9x5150zps/IXCE/"
    "dOjQ4sVvvrP6nbKakCgsLJw0eVL79u1m3Tbrlptvjf3kpMkTozS4YsXK1+a/tn3b9mhMDh48OD8akzVdvPyKy0eN+t6RI0fmzXv1"
    "7ZVv7927t2Gjhv379b966lWFhYU3zrjxt7/5beYeRa1avfqdsrKy/fv3N45aNWlS+/btZs2adcsttyb/yqhR39u9u+x///f/bdjw"
    "ydGjR/v16ztjxo35+fnXXDP1Zz87Aas33TSjc+fOVVVVTz319OpVqw8fruzSpfN111976aWjnLh6+fIVy5ev+O3vHuzZs8dDD81+"
    "c/ES52uKSy4ZuXPnzj/96c8bN26sV69eUdHQ6667pl27gocf/n2bNm1eeWXem28u3bt3b7t27W6++cauXbtcf/21paVrYrF3xRXj"
    "Ro/+3pEjR+bOfXXlylX79u5t1Khhv/79pk69qrCw+4ybpv/mwd9pWgHJ8TBmPuBRnAgFm7NdifkWgKgpnsHQnMHMqgKTnLEJAol5"
    "FFj7sf/AgfnNmiml3lm1Kvov/7dv38YNGwp79hw2fLgTIIx9GCLed88927Zujf7ff5SWfr5r18OPPXZa69ZDi4uj3NWkadPLJ0xQ"
    "Sv36/vv/9cEH0Z88evToimXLPtuy5fezZw8pKnrumWf27t0b/U/PPv10fFv7y8vXlJRsWL/+0T/+sXOXLp27dt1SeyOcBsU06z3g"
    "9NNjm1Rjz/Gvv37koYf27dunlHr2mWdSuGjdumoXdemyJWkXYkVFxY9mzTp48GBMqUgkcvuPf9x/4MBIJBItCzdv3vyyceOUUn+b"
    "M+e5vzwbU2rzps2bN21OaWpFRcUdM2MfC2tK10Qiubf/5Ef9Bw6IfaxS6tmnEwzev6akdMP69Y/+8fHOXTp36dol4fMrKirumHlb"
    "zNp0H9u2oO3Z53xbKfWH2Y+sWLY8KtXGjZ/ce9fdj/3piZYtW3pRoXXr1sXDhimlnvnz06/Omxf9x62fbf3Fz++77/77+w/oP2ny"
    "5GQgrKqquvvOu2LBnOH5+OOPt2/f3r59+6Li4oULFsT+vWu3bp27dD527NhbS5ZGcy1mydNJlvwivSVZfX1RVVV1108cmV1rHED8"
    "6T0/3bZ1W0ymz3d9/shjj5zW+rSi4qI331yS4XefefovCSFRWlK6fv36x//4WHxING/efOy4sUqpl+a89Oxf/noiJjdvrt5qW9PF"
    "pk2bjh9/hVLql7/8VXSfbfQnly9fvmXLlodnP1RUNPTZvzybuY9PP1PLqvLy/SUlpevWrf/jHx/r0qVzly5dNqfKrFmzTsRqaema"
    "SCTy4x//aOCJWIU2bdqce+53lFKPzP7DW28ti/7k+vUb7vzJ3X968vHmzZsHOp4cPHhw1qwf/fe//63+EmTe/K5duxYXDy0oKHj2"
    "2edefLG6vLxp06bf/OZ3TzzxWKtWp7Rv327btu1KqaZNm0yYcIVS6pf3P/BBvFeXrdiy5bPZs/9fUdHQvzzz12wjJ0wIlJcCyS5o"
    "3Wqdo89m/95S9fmsCwyu0xDQ+So018nxFyrS67Tpd0BlUCS4YqBLj7LVorYfh51/vlLq8127YiAXg8OBZ5xxcpMmzgexNSUl8R+i"
    "lNq5Y0f0o84866zov5w1eHBeXt6WzZtjNBh7tm/btnnTJgDo1adP5h4c+PLL9evWKaW6d++e3bgMLvfIZ/g9nSuKo0eP7tq5c/HC"
    "hbfedNPK5cszuejAgWoXFRYm/9e3liyJrVmjz0f//rdSKhKJNG/Rolqps8+ORCIVFRUvvfCiQ/PeenPJwYMV8d76z4mPbV6Xpgc2"
    "rFuvlOqWdJrRW28mWpvyY88YNEgptaesbOWKFfGCVVVVzf2717NYzzxrEAAcOHBgwRtvJFDQC88/r5QqaNfutNNOS/it5cuWO18c"
    "L3xjgVLqwhG19iiOGDFCKfXO6ncqKiqikTaoLkvaVVvifg7LyuzYU1pSGqPB6LNjx47Vq1ZHbXZhxoEvD6xft74mzZVSavDZg6Mx"
    "+eILczJn5uDBZ+Xl5W3ZvCVGgyfGme3bN2/aDAC9e/d2Y9WBA+vWrVdKFRamOHZryZKlCbH673//JxqrLVq0iNo6aNCZALBnzxfL"
    "ltVK4SNHjrz891eCXgYuWbI0RoM1LLo+Gj9z575aa/TeuSval1atWkWdffbgwXl5eZs3b/kg2avbtm+KerVPL9oLH5efJftFdSy/"
    "/ICsSOA2B6kcwVIh2FmAgjryCoiYZToBEvYoGObcbzVsOGjwYBVXHow+JatXX/v979erV29ocfHrr77qUKnNqYp1mzdtGlJUVNCu"
    "XfT/durSRSnVqXPneQsWKKUATrg09vdoxTL29Ovff/gFF3Tt3r1Z8+bREyBjT5OmTR3JBS7FBgLhGruHMMNT7aJu3VK4KBXSJx8e"
    "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"
    "TJwyeeKUySeW/jt27Nmz58xBiWfZvzF/flFxcduCgnGTrx83+fpqryC+/Le/jb088SvtlcuXX3TJJV26dv3Dn/5UvcDatWvGDTe4"
    "8G6s3RumT79h+vTM7fr7nHDR5MkTJ9ftoqzy4vm/Pndy0ybfvfDCYcPPGzb8vPj/9M/33ndpcEl2mmb1PDp7duu2bdq3bz/9phnT"
    "b5oR+/f5r84fNXqUUip2aaGL57FHH215SsvevXtPufqqKVdfFf+fXnj++RIHN3Y6EeL48W8WL1585cQrc3JyNqxfv7X2RQ7R5w+P"
    "/iFqyVVXX3VVgiXPvVDyTkn8v7w2/7XiYcVtC9pOmz5t2vRpseD8+0t/H3fFOB9DcdGCRcMvGH5nbV46dOjQA7/6deZb6UtLS9eu"
    "/bhPn96TJ0+aPHlS7N937NixZ8+eQbVD4rm/PtekSZMLL/zuecPPO692TL5fOybnzHmpfoMGY8ZcVlRUVFRUlGGcSZnmpaVr0li1"
    "c8+ePYMGnekpUB/5Q5s2bTp16njjjdNuvHFa7N9ffXX+6NGjHH7I8mUrLrnk4q5duz755OMx1Lz++mmBTnhzXnypQf36Y8ZeVlQ8"
    "tKh4aDqvFg8rXrFihQFrO1l91a0FsVVVxOCFX1YQ52gvqGFYKBfHCwSKFtnPWtH9ovv27k2+DzD+895ctOi673//rLPPbtiw4Vdf"
    "fZX5Mz9eu3bB669fPmFC7759T27c+ODBgx/8859znn/+//bti9cCUf3lz0+vfnvViItH9u7Tp3mLFgCwf//+fV/s/deHH/6jtDSm"
    "GCL+/J57xowbN6SoqFWrVlXHju0pK1tTUvLq3LnTZsxINqCysvLRX9854tLxfQYMOrlJ/leHD2/csGHu3/9eXl6eDGabPv30Fz/9"
    "6egxYzp16tSwUaMM5+bV6eDKysof3377hIkTBw0e3Cy/ut1X0rTrs/JZuiirvPjmm28efWj26pWrLrxoRGHPHk2bNv3qq6++2PPF"
    "++++uyTjPeOZDf7Z3feOuXzckKKhp1YbvKe0pOTVuXOn12Fw3U9FRcXtM2eNGTv23KFDWrZseeTIkS2bN89/df4Xe/aMGj3q+PHj"
    "yVtVnT+VlZV3/+TO4eefXzSsuEOHDvXr16+oqNiwfv3rr7227uN1Po5uby5efOXEK5VSC2ofJxNvyV0/uWv4+cOLa1my4bX5KSyp"
    "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"
)

FAVICON_B64 = (
    "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"
    "gg=="
)


HTML_TEMPLATE = r"""<!doctype html>
<html lang="{{ context.lang }}" dir="ltr" data-theme="light">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">
  <meta id="themeColor" name="theme-color" content="#f6f2ea">
  <meta name="color-scheme" content="light dark">
  <meta name="robots" content="index,follow,max-image-preview:large,max-snippet:-1,max-video-preview:-1">
  <meta name="googlebot" content="index,follow,max-image-preview:large,max-snippet:-1">
  <meta name="author" content="{{ app_name }}">
  <meta name="application-name" content="{{ app_name }}">
  <meta name="apple-mobile-web-app-title" content="{{ app_name }}">
  <meta name="mobile-web-app-capable" content="yes">
  <meta name="apple-mobile-web-app-capable" content="yes">
  <meta name="apple-mobile-web-app-status-bar-style" content="default">
  <meta name="format-detection" content="telephone=no">
  <meta name="description" content="{{ seo.description }}">
  <meta name="keywords" content="Panchang, Panchangam, {{ context.place }}, Tithi, Nakshatra, Yoga, Karana, Choghadiya, Hora, Muhurta, Lagna, sunrise, sunset">

  <title>{{ seo.title }}</title>
  <script src="/global.js" defer></script>
  <link rel="canonical" href="{{ seo.canonical }}">
  {% for code, href in seo.alternates.items() %}<link rel="alternate" hreflang="{{ code }}" href="{{ href }}">
  {% endfor %}
  <link rel="alternate" type="application/json" title="Machine-readable Panchang" href="{{ api_href }}">
  <link rel="alternate" type="text/plain" title="AI-readable site guide" href="{{ root }}/llms.txt">
  <link rel="manifest" href="{{ root }}/manifest.webmanifest">
  <link rel="icon" href="{{ root }}/favicon.ico" sizes="any">
  <link rel="icon" type="image/png" href="{{ root }}/icon-192.png" sizes="192x192">
  <link rel="apple-touch-icon" href="{{ root }}/icon-192.png">

  <meta property="og:type" content="website">
  <meta property="og:site_name" content="{{ app_name }}">
  <meta property="og:locale" content="{{ og_locale }}">
  <meta property="og:title" content="{{ seo.title }}">
  <meta property="og:description" content="{{ seo.description }}">
  <meta property="og:url" content="{{ seo.canonical }}">
  <meta property="og:image" content="{{ seo.og_image }}">
  <meta property="og:image:secure_url" content="{{ seo.og_image }}">
  <meta property="og:image:type" content="image/png">
  <meta property="og:image:width" content="1200">
  <meta property="og:image:height" content="630">
  <meta property="og:image:alt" content="{{ seo.title }} — current Panchang timings">
  <meta name="twitter:card" content="summary_large_image">
  <meta name="twitter:title" content="{{ seo.title }}">
  <meta name="twitter:description" content="{{ seo.description }}">
  <meta name="twitter:image" content="{{ seo.og_image }}">
  <meta name="twitter:image:alt" content="{{ seo.title }} — current Panchang timings">

  <script nonce="{{ nonce }}">try{const t=localStorage.getItem('panchang-theme');document.documentElement.dataset.theme=t==='dark'?'dark':'light'}catch(_){document.documentElement.dataset.theme='light'}</script>
  <style nonce="{{ nonce }}">
  {{ css | safe }}
  .sr-only { position:absolute!important; width:1px!important; height:1px!important; padding:0!important; margin:-1px!important; overflow:hidden!important; clip:rect(0,0,0,0)!important; white-space:nowrap!important; border:0!important; }
  .noscript-card { position:fixed; z-index:100; inset:auto 12px 12px; padding:10px 13px; border:1px solid var(--line-strong); border-radius:12px; color:var(--text); background:var(--surface-strong); font-size:12px; box-shadow:var(--shadow); }
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
      {% for section in data.sections %}
      {% if section.reserved %}
      <section class="metric-row reserved-row" data-section="reserved" aria-hidden="true">
        <div class="reserved-label"></div>
        <div class="reserved-space"></div>
      </section>
      {% else %}
      <section class="metric-row" data-section="{{ section.key }}" itemscope itemtype="https://schema.org/Observation">
        <div class="metric-label">
          <span class="metric-icon" aria-hidden="true">{{ section.icon }}</span>
          <h2 itemprop="variableMeasured">{{ section.label }}</h2>
        </div>
        <div class="timeline-wrap">
          <div class="timeline" tabindex="0" role="list" aria-label="{{ section.label }} — {{ data.ui.timeline_hint }}">
            {% for item in section["items"] %}
            <article class="moment {{ item.quality }}{% if item.current %} is-current{% endif %}" role="listitem"{% if item.current %} aria-current="true"{% endif %} aria-label="{{ item.title }}. {{ item.time }}">
              <strong class="moment-title" itemprop="value">{{ item.title }}</strong>
              <time class="moment-time"{% if item.start %} datetime="{{ item.start }}"{% endif %}>{{ item.time }}</time>
              <span class="badges">
                {% if item.quality == 'auspicious' %}<span class="badge good">{{ data.ui.good }}</span>{% endif %}
                {% if item.quality == 'inauspicious' %}<span class="badge bad">{{ data.ui.avoid }}</span>{% endif %}
                {% if item.detail and item.detail == data.ui.mixed %}<span class="badge neutral">{{ item.detail }}</span>{% endif %}
              </span>
            </article>
            {% endfor %}
          </div>
        </div>
      </section>
      {% endif %}
      {% endfor %}
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
        <div class="field">
          <label for="placeInput" data-i18n="place">{{ data.ui.place }}</label>
          <div class="input-shell">
            <input id="placeInput" type="search" value="{{ context.place }}" autocomplete="off" enterkeyhint="search" spellcheck="false" data-i18n-placeholder="search_place" placeholder="{{ data.ui.search_place }}" aria-controls="placeResults" aria-autocomplete="list">
          </div>
          <div class="place-results" id="placeResults" role="listbox" aria-live="polite"></div>
        </div>

        <div class="form-grid">
          <div class="field">
            <label for="dateInput" data-i18n="date">{{ data.ui.date }}</label>
            <input id="dateInput" type="date" min="1600-01-01" max="2400-12-31" value="{{ context.date.isoformat() }}">
          </div>
          <div class="field">
            <label for="timeInput" data-i18n="time">{{ data.ui.time }}</label>
            <input id="timeInput" type="time" step="60" value="{{ context.time.strftime('%H:%M') }}">
          </div>
        </div>

        <div class="field">
          <label for="languageInput" data-i18n="language">{{ data.ui.language }}</label>
          <select id="languageInput">
            {% for language in data.languages %}<option value="{{ language.code }}"{% if language.code == context.lang %} selected{% endif %}>{{ language.native }} — {{ language.name }}</option>{% endfor %}
          </select>
        </div>

        <div class="field theme-field">
          <span class="field-label" data-i18n="appearance">{{ data.ui.appearance }}</span>
          <div class="theme-toggle" role="group" aria-label="{{ data.ui.appearance }}">
            <button class="theme-choice" type="button" data-theme-choice="light" aria-pressed="true">
              <svg viewBox="0 0 24 24" aria-hidden="true"><circle cx="12" cy="12" r="4"/><path d="M12 2v2M12 20v2M4.93 4.93l1.42 1.42M17.66 17.66l1.41 1.41M2 12h2M20 12h2M4.93 19.07l1.42-1.42M17.66 6.34l1.41-1.41"/></svg>
              <span data-i18n="light">{{ data.ui.light }}</span>
            </button>
            <button class="theme-choice" type="button" data-theme-choice="dark" aria-pressed="false">
              <svg viewBox="0 0 24 24" aria-hidden="true"><path d="M21 12.8A9 9 0 1 1 11.2 3a7 7 0 0 0 9.8 9.8Z"/></svg>
              <span data-i18n="dark">{{ data.ui.dark }}</span>
            </button>
          </div>
        </div>

        <div class="switch-row">
          <label for="liveInput" data-i18n="live_time">{{ data.ui.live_time }}</label>
          <label class="switch" aria-label="{{ data.ui.live_time }}">
            <input id="liveInput" type="checkbox"{% if context.live %} checked{% endif %}>
            <span class="switch-track" aria-hidden="true"></span>
          </label>
        </div>

        <button class="location-button" id="locationButton" type="button" data-i18n="use_location">{{ data.ui.use_location }}</button>
        <p class="sheet-note">{{ data.ui.calculation_note }}</p>
        <p class="sheet-note">{{ data.ui.geocode_attribution }}</p>
      </div>
      <div class="sheet-actions">
        <button class="action-button secondary" id="cancelButton" type="button" data-i18n="cancel">{{ data.ui.cancel }}</button>
        <button class="action-button primary" type="submit" data-i18n="apply">{{ data.ui.apply }}</button>
      </div>
    </form>
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
        "form-action 'self'; img-src 'self' data:; font-src 'self' data:; "
        f"style-src 'self' 'nonce-{nonce}'; style-src-attr 'unsafe-inline'; "
        f"script-src 'self' 'nonce-{nonce}'; script-src-attr 'none'; "
        "connect-src 'self'; manifest-src 'self'; worker-src 'self'; upgrade-insecure-requests"
    )
    response.headers["Cache-Control"] = "public, max-age=45, stale-while-revalidate=120" if context["live"] else "public, max-age=300, stale-while-revalidate=1800"
    return response


@app.after_request
def add_common_headers(response: Response) -> Response:
    response.headers.setdefault("X-Content-Type-Options", "nosniff")
    response.headers.setdefault("Referrer-Policy", "strict-origin-when-cross-origin")
    response.headers.setdefault("Permissions-Policy", "geolocation=(self), camera=(), microphone=(), payment=(), usb=()")
    response.headers.setdefault("Cross-Origin-Opener-Policy", "same-origin")
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



def distance_km(latitude_a: float, longitude_a: float, latitude_b: float, longitude_b: float) -> float:
    """Great-circle distance used to resolve common cities without a network call."""
    radius = 6371.0088
    lat_a = math.radians(latitude_a)
    lat_b = math.radians(latitude_b)
    delta_lat = lat_b - lat_a
    delta_lon = math.radians(longitude_b - longitude_a)
    hav = math.sin(delta_lat / 2) ** 2 + math.cos(lat_a) * math.cos(lat_b) * math.sin(delta_lon / 2) ** 2
    return radius * 2 * math.atan2(math.sqrt(hav), math.sqrt(max(0.0, 1.0 - hav)))


def nearby_catalogue_place(latitude: float, longitude: float, maximum_km: float = 35.0) -> dict[str, Any] | None:
    nearest: tuple[float, str, dict[str, Any]] | None = None
    for slug, place in POPULAR_PLACES.items():
        distance = distance_km(latitude, longitude, float(place["latitude"]), float(place["longitude"]))
        if nearest is None or distance < nearest[0]:
            nearest = (distance, slug, place)
    if nearest is None or nearest[0] > maximum_km:
        return None
    _distance, slug, place = nearest
    return {
        "name": str(place["name"]),
        "display_name": f"{place['name']}, {place.get('country', '')}".strip(", "),
        "latitude": round(latitude, 6),
        "longitude": round(longitude, 6),
        "country": str(place.get("country") or ""),
        "slug": slug,
        "source": "built-in",
    }


@lru_cache(maxsize=1024)
def remote_reverse_place(latitude_key: int, longitude_key: int, lang: str) -> dict[str, Any]:
    latitude = latitude_key / 10000.0
    longitude = longitude_key / 10000.0
    endpoint = os.getenv("REVERSE_GEOCODING_API_URL", "https://nominatim.openstreetmap.org/reverse")
    params: dict[str, Any] = {
        "format": "jsonv2",
        "lat": f"{latitude:.4f}",
        "lon": f"{longitude:.4f}",
        "zoom": 10,
        "addressdetails": 1,
        "namedetails": 1,
        "accept-language": lang if lang in LANGUAGES else "en",
    }
    contact = os.getenv("GEOCODING_CONTACT_EMAIL", "").strip()
    if contact:
        params["email"] = contact
    response = requests.get(
        endpoint,
        params=params,
        headers={"Accept": "application/json", "User-Agent": f"{APP_NAME}/{APP_VERSION} (+{site_root()})"},
        timeout=(2.5, 7.0),
    )
    response.raise_for_status()
    payload = response.json()
    address = payload.get("address") if isinstance(payload, dict) else {}
    if not isinstance(address, dict):
        address = {}
    locality = next((str(address.get(key) or "").strip() for key in (
        "city", "town", "village", "municipality", "borough", "suburb", "county", "state_district", "state"
    ) if str(address.get(key) or "").strip()), "")
    if not locality:
        locality = str(payload.get("name") or "").strip()
    if not locality:
        raise ValueError("Reverse geocoder did not return a locality")
    state_name = str(address.get("state") or address.get("region") or "").strip()
    country = str(address.get("country") or "").strip()
    pieces = [locality]
    if state_name and normalized_search(state_name) != normalized_search(locality):
        pieces.append(state_name)
    if country and all(normalized_search(country) != normalized_search(piece) for piece in pieces):
        pieces.append(country)
    return {
        "name": locality,
        "display_name": ", ".join(pieces),
        "latitude": round(latitude, 6),
        "longitude": round(longitude, 6),
        "country": country,
        "country_code": str(address.get("country_code") or "").upper(),
        "slug": slugify_place(locality),
        "source": "OpenStreetMap / Nominatim",
    }


def reverse_place_result(latitude: float, longitude: float, lang: str) -> dict[str, Any]:
    local = nearby_catalogue_place(latitude, longitude)
    if local:
        return local
    try:
        return remote_reverse_place(round(latitude * 10000), round(longitude * 10000), lang)
    except (requests.RequestException, ValueError, TypeError, KeyError):
        app.logger.warning("Reverse geocoding unavailable", exc_info=app.debug)
        coordinate_name = f"{latitude:.3f}, {longitude:.3f}"
        return {
            "name": coordinate_name,
            "display_name": coordinate_name,
            "latitude": round(latitude, 6),
            "longitude": round(longitude, 6),
            "country": "",
            "slug": slugify_place(coordinate_name),
            "source": "coordinates",
        }


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


@app.get("/api/reverse-place")
def reverse_place_api() -> Response:
    try:
        latitude = float(request.args.get("lat", ""))
        longitude = float(request.args.get("lon", ""))
        if not math.isfinite(latitude) or not math.isfinite(longitude) or not (-89.8 <= latitude <= 89.8) or not (-180 <= longitude <= 180):
            raise ValueError
    except (TypeError, ValueError):
        response = jsonify({"error": "Valid lat and lon query parameters are required."})
        response.status_code = 400
        response.headers["Cache-Control"] = "no-store"
        return response
    lang = (request.args.get("lang") or "en").lower().split("-")[0]
    if lang not in LANGUAGES:
        lang = "en"
    place = reverse_place_result(latitude, longitude, lang)
    response = jsonify({"place": place})
    response.headers["Cache-Control"] = "public, max-age=86400, stale-while-revalidate=604800"
    response.headers["Content-Security-Policy"] = "default-src 'none'; frame-ancestors 'none'"
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
    root = site_root()
    today = datetime.now(IST).date()
    # Current, yesterday and the next month: useful finite crawl targets rather than an infinite calendar trap.
    dates = [today - timedelta(days=1)] + [today + timedelta(days=offset) for offset in range(0, 31)]
    entries: list[str] = [
        "<?xml version=\"1.0\" encoding=\"UTF-8\"?>",
        "<urlset xmlns=\"http://www.sitemaps.org/schemas/sitemap/0.9\">",
        "  <url>",
        f"    <loc>{html.escape(root + '/', quote=True)}</loc>",
        f"    <lastmod>{today.isoformat()}</lastmod>",
        "    <changefreq>hourly</changefreq>",
        "    <priority>1.0</priority>",
        "  </url>",
    ]
    for day in dates:
        priority = "0.9" if day == today else "0.7"
        changefreq = "hourly" if day == today else "daily"
        for slug in POPULAR_PLACES:
            for lang in LANGUAGES:
                loc = f"{root}/{lang}/panchang/{slug}/{day.isoformat()}"
                entries.extend([
                    "  <url>",
                    f"    <loc>{html.escape(loc, quote=True)}</loc>",
                    f"    <lastmod>{today.isoformat()}</lastmod>",
                    f"    <changefreq>{changefreq}</changefreq>",
                    f"    <priority>{priority}</priority>",
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
        "background_color": "#fffdfa",
        "theme_color": "#f6f2ea",
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
const SHELL = ['/', '/manifest.webmanifest', '/icon-192.png', '/icon-512.png', '/favicon.ico'];
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


@lru_cache(maxsize=384)
def social_font(lang: str, size: int, bold: bool = False) -> Any:
    """Load a local font with shaping support; no remote font request is needed."""
    if ImageFont is None:
        return None
    candidates: list[str] = []
    script = _SOCIAL_SCRIPT_NAMES.get(lang)
    if script:
        weight = "Bold" if bold else "Regular"
        # Lohit faces include Latin, digits and punctuation as well as the
        # target Indic script, which prevents missing-glyph boxes in mixed
        # strings such as "11 Sept · Friday" and "1:26 AM".
        lohit_paths = {
            "Devanagari": "/usr/share/fonts/truetype/lohit-devanagari/Lohit-Devanagari.ttf",
            "Gujarati": "/usr/share/fonts/truetype/lohit-gujarati/Lohit-Gujarati.ttf",
            "Bengali": "/usr/share/fonts/truetype/lohit-bengali/Lohit-Bengali.ttf",
            "Tamil": "/usr/share/fonts/truetype/lohit-tamil/Lohit-Tamil.ttf",
            "Telugu": "/usr/share/fonts/truetype/lohit-telugu/Lohit-Telugu.ttf",
            "Kannada": "/usr/share/fonts/truetype/lohit-kannada/Lohit-Kannada.ttf",
            "Malayalam": "/usr/share/fonts/truetype/lohit-malayalam/Lohit-Malayalam.ttf",
            "Oriya": "/usr/share/fonts/truetype/lohit-oriya/Lohit-Odia.ttf",
            "Gurmukhi": "/usr/share/fonts/opentype/freefont/FreeSansBold.otf" if bold else "/usr/share/fonts/opentype/freefont/FreeSans.otf",
        }
        if script in lohit_paths:
            candidates.append(lohit_paths[script])
        candidates.extend([
            f"/usr/share/fonts/truetype/noto/NotoSans{script}-{weight}.ttf",
            "/usr/share/fonts/opentype/freefont/FreeSansBold.otf" if bold else "/usr/share/fonts/opentype/freefont/FreeSans.otf",
        ])
    else:
        candidates.extend([
            "/usr/share/fonts/opentype/inter/InterDisplay-ExtraBold.otf" if bold else "/usr/share/fonts/opentype/inter/Inter-Regular.otf",
            "/usr/share/fonts/opentype/inter/Inter-Bold.otf" if bold else "/usr/share/fonts/opentype/inter/Inter-Regular.otf",
        ])
    candidates.extend([
        "/usr/share/fonts/truetype/noto/NotoSans-Bold.ttf" if bold else "/usr/share/fonts/truetype/noto/NotoSans-Regular.ttf",
        "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf" if bold else "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
    ])
    layout = getattr(getattr(ImageFont, "Layout", object()), "RAQM", None)
    for font_path in candidates:
        if not os.path.exists(font_path):
            continue
        try:
            kwargs = {"layout_engine": layout} if layout is not None else {}
            return ImageFont.truetype(font_path, size=size, **kwargs)
        except Exception:
            continue
    try:
        return ImageFont.load_default(size=size)
    except TypeError:
        return ImageFont.load_default()


def social_text_width(draw: Any, text: str, font: Any) -> float:
    try:
        return float(draw.textlength(text, font=font))
    except Exception:
        box = draw.textbbox((0, 0), text, font=font)
        return float(box[2] - box[0])


def fit_social_font(
    draw: Any,
    text: str,
    lang: str,
    max_width: float,
    max_size: int,
    min_size: int,
    bold: bool = False,
) -> Any:
    """Return the largest local font that keeps a single line inside max_width."""
    for size in range(max_size, min_size - 1, -1):
        font = social_font(lang, size, bold)
        if social_text_width(draw, text, font) <= max_width:
            return font
    return social_font(lang, min_size, bold)


def truncate_social_text(draw: Any, text: str, font: Any, max_width: float) -> str:
    if social_text_width(draw, text, font) <= max_width:
        return text
    ellipsis = "…"
    chars = list(text)
    while chars and social_text_width(draw, "".join(chars).rstrip() + ellipsis, font) > max_width:
        chars.pop()
    return ("".join(chars).rstrip() + ellipsis) if chars else ellipsis


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
    """Render a bright 1200×630 preview using the page's default pastel theme."""
    if Image is None or ImageDraw is None or ImageFont is None:
        return base64.b64decode(OG_IMAGE_B64)

    width, height = 1200, 630
    top_color = (255, 253, 248)
    bottom_color = (238, 246, 243)
    canvas = Image.new("RGBA", (width, height), top_color + (255,))
    draw = ImageDraw.Draw(canvas)
    for y in range(height):
        draw.line((0, y, width, y), fill=_mix_rgb(top_color, bottom_color, y / max(1, height - 1)))

    glow = Image.new("RGBA", canvas.size, (0, 0, 0, 0))
    glow_draw = ImageDraw.Draw(glow)
    glow_draw.ellipse((-250, -260, 430, 430), fill=(91, 205, 174, 72))
    glow_draw.ellipse((330, -330, 920, 300), fill=(255, 213, 88, 54))
    glow_draw.ellipse((900, -210, 1480, 390), fill=(232, 111, 154, 55))
    glow_draw.ellipse((760, 420, 1420, 890), fill=(103, 157, 222, 35))
    glow = glow.filter(ImageFilter.GaussianBlur(92)) if ImageFilter is not None else glow
    canvas = Image.alpha_composite(canvas, glow)
    draw = ImageDraw.Draw(canvas)

    margin = 34
    header_box = (margin, 24, width - margin, 148)
    draw.rounded_rectangle(header_box, radius=31, fill=(255, 255, 255, 236), outline=(42, 50, 61, 30), width=2)
    icon_box = (54, 45, 134, 125)
    draw.rounded_rectangle(icon_box, radius=24, fill=(218, 246, 236, 255), outline=(22, 143, 121, 92), width=2)
    _draw_social_sun(draw, (94, 85), 14, (205, 143, 15, 255))

    lang = context["lang"]
    title_text = tr(lang, "panchang")
    title_font = fit_social_font(draw, title_text, lang, 620, 49, 36, True)
    draw.text((158, 43), title_text, font=title_font, fill=(22, 24, 32, 255))

    subtitle = f"{context['place']}  •  {format_date_label(context['date'], lang)}  •  {format_clock(context['at'])}"
    subtitle_font = fit_social_font(draw, subtitle, lang, 780, 27, 19, True)
    subtitle_text = truncate_social_text(draw, subtitle, subtitle_font, 780)
    draw.text((158, 98), subtitle_text, font=subtitle_font, fill=(83, 91, 103, 255))

    live_text = tr(lang, "live") if context.get("social_live", context.get("live")) else tr(lang, "selected")
    live_font = social_font(lang, 16, True)
    live_width = social_text_width(draw, live_text, live_font)
    live_left = width - margin - live_width - 38
    live_box = (live_left, 45, width - margin - 16, 79)
    draw.rounded_rectangle(live_box, radius=17, fill=(201, 241, 228, 255), outline=(22, 143, 121, 95), width=1)
    draw.text((live_left + 19, 53), live_text, font=live_font, fill=(18, 101, 84, 255))

    timezone_text = context["timezone"]
    timezone_font = social_font("en", 14, True)
    timezone_width = social_text_width(draw, timezone_text, timezone_font)
    draw.text((width - margin - timezone_width - 16, 106), timezone_text, font=timezone_font, fill=(103, 111, 123, 255))

    accents = [
        (207, 143, 13), (22, 143, 121), (216, 82, 130), (122, 102, 220), (226, 105, 85),
        (204, 123, 32), (37, 141, 164), (108, 100, 216), (74, 118, 200),
    ]
    fills = [
        (255, 244, 205), (220, 246, 237), (251, 224, 235), (232, 230, 255), (255, 229, 222),
        (255, 238, 213), (221, 243, 246), (231, 229, 255), (225, 235, 252),
    ]
    card_gap_x = 16
    card_gap_y = 8
    card_width = (width - margin * 2 - card_gap_x) // 2
    card_height = 76
    cards_top = 164

    visible_sections = [section for section in data["sections"] if not section.get("reserved")][:9]
    for index, section in enumerate(visible_sections):
        column = index % 2
        row = index // 2
        x1 = margin + column * (card_width + card_gap_x)
        y1 = cards_top + row * (card_height + card_gap_y)
        x2 = x1 + card_width
        y2 = y1 + card_height
        accent = accents[index % len(accents)]
        fill = fills[index % len(fills)]
        item = current_or_focused(section.get("items", []))
        quality = item.get("quality", "neutral") if item else "neutral"
        if quality == "auspicious":
            fill = (218, 247, 235)
            border = (19, 135, 111, 205)
        elif quality == "inauspicious":
            fill = (255, 228, 235)
            border = (200, 66, 97, 205)
        else:
            border = accent + (155,)

        draw.rounded_rectangle((x1, y1, x2, y2), radius=18, fill=fill + (246,), outline=border, width=2)
        draw.rounded_rectangle((x1 + 1, y1 + 1, x1 + 7, y2 - 1), radius=4, fill=accent + (255,))
        circle = (x1 + 17, y1 + 18, x1 + 55, y1 + 56)
        draw.ellipse(circle, fill=accent + (24,), outline=accent + (120,), width=2)
        number_text = str(index + 1)
        number_font = social_font("en", 15, True)
        number_box = draw.textbbox((0, 0), number_text, font=number_font)
        number_x = x1 + 36 - (number_box[2] - number_box[0]) / 2
        number_y = y1 + 37 - (number_box[3] - number_box[1]) / 2 - number_box[1]
        draw.text((number_x, number_y), number_text, font=number_font, fill=accent + (255,))

        label_x = x1 + 68
        content_right = x2 - 15
        label = str(section.get("label", ""))
        label_font = fit_social_font(draw, label, lang, 285, 16, 12, True)
        label = truncate_social_text(draw, label, label_font, 285)
        draw.text((label_x, y1 + 7), label, font=label_font, fill=accent + (255,))

        badge_text = ""
        if quality == "auspicious":
            badge_text = tr(lang, "good")
        elif quality == "inauspicious":
            badge_text = tr(lang, "avoid")
        if badge_text:
            badge_font = fit_social_font(draw, badge_text, lang, 150, 13, 10, True)
            badge_text = truncate_social_text(draw, badge_text, badge_font, 150)
            badge_width = social_text_width(draw, badge_text, badge_font) + 20
            badge_color = (19, 135, 111) if quality == "auspicious" else (200, 66, 97)
            badge_left = x2 - 13 - badge_width
            draw.rounded_rectangle((badge_left, y1 + 6, x2 - 13, y1 + 30), radius=12, fill=badge_color + (255,))
            badge_box = draw.textbbox((0, 0), badge_text, font=badge_font)
            badge_y = y1 + 18 - (badge_box[3] - badge_box[1]) / 2 - badge_box[1]
            draw.text((badge_left + 10, badge_y), badge_text, font=badge_font, fill=(255, 255, 255, 255))

        value = str(item.get("title", "—"))
        value_width = max(120, content_right - label_x)
        value_font = fit_social_font(draw, value, lang, value_width, 22, 16, True)
        value = truncate_social_text(draw, value, value_font, value_width)
        draw.text((label_x, y1 + 27), value, font=value_font, fill=(24, 27, 35, 255))

        timing = str(item.get("time", ""))
        timing_font = fit_social_font(draw, timing, lang, value_width, 14, 10, False)
        timing = truncate_social_text(draw, timing, timing_font, value_width)
        draw.text((label_x, y1 + 54), timing, font=timing_font, fill=(92, 99, 111, 255))

    footer_y = 596
    draw.line((margin + 8, footer_y - 10, width - margin - 8, footer_y - 10), fill=(53, 60, 70, 30), width=1)
    site_text = site_root().replace("https://", "").replace("http://", "").split("/")[0] or APP_NAME
    site_font = social_font("en", 15, True)
    draw.text((margin + 8, footer_y), site_text, font=site_font, fill=(174, 115, 11, 255))
    footer_message = f"{TIMELINE_FUTURE_ITEMS}+ upcoming values in every timeline  •  tap to explore"
    footer_font = social_font("en", 15, True)
    footer_width = social_text_width(draw, footer_message, footer_font)
    draw.text((width - margin - 8 - footer_width, footer_y), footer_message, font=footer_font, fill=(66, 116, 126, 255))

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


@app.get("/og.png")
def open_graph_image() -> Response:
    try:
        context = resolve_context()
        context["social_live"] = request.args.get("mode") == "live"
        data = build_panchang(context)
        payload = render_social_image(context, data)
        response = Response(payload, mimetype="image/png")
        response.headers["Content-Disposition"] = 'inline; filename="panchang-social.png"'
        response.headers["Cache-Control"] = "public, max-age=300, stale-while-revalidate=3600"
        response.headers["Content-Security-Policy"] = "default-src 'none'; frame-ancestors 'none'"
        response.headers["X-Content-Type-Options"] = "nosniff"
        return response
    except Exception:
        app.logger.exception("Dynamic social image rendering failed")
        fallback = Response(base64.b64decode(OG_IMAGE_B64), mimetype="image/png")
        fallback.headers["Content-Disposition"] = 'inline; filename="panchang-social.png"'
        fallback.headers["Cache-Control"] = "public, max-age=300"
        fallback.headers["Content-Security-Policy"] = "default-src 'none'; frame-ancestors 'none'"
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
                    "description": "Returns prior, active and at least 12 upcoming intervals for every Panchang timeline.",
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
            "/api/reverse-place": {
                "get": {
                    "operationId": "reversePlace",
                    "summary": "Resolve latitude and longitude to a city name",
                    "parameters": [
                        {"name": "lat", "in": "query", "required": True, "schema": {"type": "number", "minimum": -89.8, "maximum": 89.8}},
                        {"name": "lon", "in": "query", "required": True, "schema": {"type": "number", "minimum": -180, "maximum": 180}},
                        {"name": "lang", "in": "query", "schema": {"type": "string", "enum": language_enum, "default": "en"}},
                    ],
                    "responses": {"200": {"description": "Resolved city"}, "400": {"description": "Invalid coordinates"}},
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
                        "reserved": {"type": "boolean", "description": "Empty presentation row"},
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
    response = jsonify({"status": "ok", "app": APP_NAME, "version": APP_VERSION, "time": datetime.now(UTC).isoformat()})
    response.headers["Cache-Control"] = "no-store"
    response.headers["X-Robots-Tag"] = "noindex, nofollow"
    response.headers["Content-Security-Policy"] = "default-src 'none'; frame-ancestors 'none'"
    return response


if __name__ == "__main__":
    port = int(os.getenv("PORT", "10000"))
    debug = os.getenv("FLASK_DEBUG", "0") in {"1", "true", "True", "yes"}
    app.run(host="0.0.0.0", port=port, debug=debug)
