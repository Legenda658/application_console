import cv2
import numpy as np
from PIL import Image, ImageDraw, ImageFont
from datetime import datetime
import os
import platform
import sys
import requests
import json
import base64
import io
import tempfile
import time
import serial
import re
import threading
if platform.system() == 'Windows':
    import locale
    locale.setlocale(locale.LC_ALL, 'Russian_Russia.1251')
else:
    sys.stdout.reconfigure(encoding='utf-8')
API_TOKEN = ''  
CAMERA_INDEX = 0
SERVER_URL = "http://farm429.online/api/upload-image.php"
SENSOR_API_URL = "http://farm429.online/api/save-sensor-data.php"
LED_API_URL = "http://farm429.online/api/get-lamp-state.php"
CURTAINS_API_URL = "http://farm429.online/api/get-curtains-state.php"
THRESHOLDS_API_URL = "http://farm429.online/api/get-thresholds.php"
MAX_ID_API_URL = "http://farm429.online/api/get-max-sensor-id.php"
SERIAL_PORT = 'COM10'
BAUD_RATE = 9600
SAVE_LOCAL = True
LOCAL_PATH = "photos"
OUTPUT_PATH = "plant_analysis.jpg"
FONT_PATH = "arial.ttf"
THRESHOLDS_PRINT_INTERVAL = 60
if SAVE_LOCAL and not os.path.exists(LOCAL_PATH):
    os.makedirs(LOCAL_PATH)
last_temperature = 0
last_humidity = 0
last_soil_moisture = 0
last_light_level = 0
last_co2 = 400  
last_pressure = 1013.25  
last_led_state = None
last_curtains_state = None
last_thresholds = None
last_thresholds_print_time = 0
auth_error_occurred = False
last_used_id = 0  
DISEASES_DB = {
    "yellow_leaves": {"name": "Хлороз", "description": "Пожелтение листьев", "causes": ["Недостаток железа", "Переувлажнение", "Недостаток азота"], "solutions": ["Добавить железосодержащие удобрения", "Уменьшить полив", "Внести азотные удобрения"]},
    "brown_spots": {"name": "Грибковое заболевание", "description": "Коричневые пятна на листьях", "causes": ["Грибковая инфекция", "Избыточная влажность", "Плохая вентиляция"], "solutions": ["Обработать фунгицидами", "Улучшить вентиляцию", "Удалить пораженные листья"]},
    "white_powder": {"name": "Мучнистая роса", "description": "Белый налет на листьях", "causes": ["Грибковая инфекция", "Высокая влажность", "Резкие перепады температуры"], "solutions": ["Обработать фунгицидами", "Снизить влажность воздуха", "Обеспечить стабильную температуру"]},
    "leaf_curl": {"name": "Курчавость листьев", "description": "Деформация и скручивание листьев", "causes": ["Вирусная инфекция", "Недостаток кальция", "Повреждение насекомыми"], "solutions": ["Удалить пораженные части", "Внести кальциевые удобрения", "Обработать инсектицидами"]},
    "black_spots": {"name": "Черная пятнистость", "description": "Черные пятна на листьях", "causes": ["Грибковая инфекция", "Высокая влажность", "Недостаточная циркуляция воздуха"], "solutions": ["Обработать фунгицидами", "Улучшить проветривание", "Удалить пораженные листья"]},
    "wilting": {"name": "Увядание", "description": "Общее увядание растения", "causes": ["Недостаток воды", "Корневая гниль", "Бактериальная инфекция"], "solutions": ["Проверить режим полива", "Проверить корневую систему", "Обработать фунгицидами"]},
    "mosaic": {"name": "Мозаичная болезнь", "description": "Мозаичный узор на листьях", "causes": ["Вирусная инфекция", "Переносчики вирусов"], "solutions": ["Удалить пораженные растения", "Бороться с насекомыми-переносчиками"]}
}
PESTS_DB = {
    "aphids": {"name": "Тля", "description": "Мелкие насекомые на листьях и стеблях", "damage": "Высасывают сок из растения, вызывают деформацию листьев", "solutions": ["Обработать инсектицидами", "Использовать мыльный раствор", "Привлечь естественных хищников"]},
    "whitefly": {"name": "Белокрылка", "description": "Мелкие белые летающие насекомые", "damage": "Высасывают сок, выделяют медвяную росу, переносят вирусы", "solutions": ["Использовать желтые липкие ловушки", "Обработать инсектицидами", "Регулярно осматривать нижнюю сторону листьев"]},
    "thrips": {"name": "Трипсы", "description": "Мелкие удлиненные насекомые", "damage": "Повреждают листья и цветы, переносят вирусы", "solutions": ["Обработать инсектицидами", "Использовать синие липкие ловушки", "Удалять сорняки"]},
    "mealybugs": {"name": "Мучнистые червецы", "description": "Белые пушистые насекомые", "damage": "Высасывают сок, выделяют медвяную росу", "solutions": ["Обработать спиртовым раствором", "Использовать системные инсектициды", "Изолировать пораженные растения"]},
    "scale_insects": {"name": "Щитовки", "description": "Неподвижные насекомые под защитным щитком", "damage": "Высасывают сок, ослабляют растение", "solutions": ["Механически удалить", "Обработать масляными препаратами", "Использовать системные инсектициды"]},
    "caterpillars": {"name": "Гусеницы", "description": "Личинки бабочек различных размеров", "damage": "Объедают листья, стебли и плоды", "solutions": ["Собирать вручную", "Использовать биологические препараты", "Обработать инсектицидами"]}
}
LEAF_COLORS = {
    "healthy_green": {"lower": np.array([35, 30, 30]), "upper": np.array([85, 255, 255]), "name": "здоровый зеленый"},
    "yellow": {"lower": np.array([20, 30, 30]), "upper": np.array([35, 255, 255]), "name": "желтый"},
    "brown": {"lower": np.array([10, 30, 10]), "upper": np.array([20, 255, 255]), "name": "коричневый"},
    "light_green": {"lower": np.array([35, 30, 30]), "upper": np.array([85, 100, 255]), "name": "светло-зеленый"}
}
def get_api_token():
    """Запрашивает API токен у пользователя"""
    print("\n💻 НАСТРОЙКА API ТОКЕНА")
    print("────────────────────────────────────────")
    print("Для работы программы требуется API токен.")
    print("Если у вас нет токена, получите его на сайте: https://farm429.online/get_token.php")
    print("────────────────────────────────────────")
    token = input("Введите ваш API токен: ").strip()
    while not token:
        print("❌ Токен не может быть пустым!")
        token = input("Введите ваш API токен: ").strip()
    return token
def print_auth_error():
    """Выводит сообщение об ошибке авторизации"""
    global auth_error_occurred
    if not auth_error_occurred:
        print()
        print("⛔ ОШИБКА АВТОРИЗАЦИИ ⛔")
        print("────────────────────────────────────────")
        print("Проверьте токен авторизации: https://farm429.online/get_token.php")
        print("────────────────────────────────────────")
        print()
        auth_error_occurred = True
        sys.exit(1)
def take_photo():
    """Сделать фото с камеры"""
    cap = cv2.VideoCapture(CAMERA_INDEX)
    if not cap.isOpened():
        raise Exception("Ошибка подключения камеры")
    ret, frame = cap.read()
    cap.release()
    if not ret:
        raise Exception("Ошибка получения изображения с камеры")
    return frame
def upload_to_server(original_image, analysis_image, text="Анализ состояния растений"):
    """Загрузить фото на сервер"""
    try:
        timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        orig_filename = f"farm_photo_{timestamp}.jpg"
        analysis_filename = f"farm_analysis_{timestamp}.jpg"
        cv2.imwrite(orig_filename, original_image)
        cv2.imwrite(analysis_filename, analysis_image)
        if not os.path.exists(orig_filename) or not os.path.exists(analysis_filename):
            raise Exception("Ошибка сохранения файлов")
        data = {
            'text': text, 
            'timestamp': datetime.now().strftime('%Y-%m-%d %H:%M:%S'), 
            'has_analysis': 'true'
        }
        headers = {
            'X-Auth-Token': API_TOKEN
        }
        with open(orig_filename, 'rb') as orig_file, open(analysis_filename, 'rb') as analysis_file:
            files = {
                'image': ('original.jpg', orig_file.read(), 'image/jpeg'),
                'analysis_image': ('analysis.jpg', analysis_file.read(), 'image/jpeg')
            }
            response = requests.post(SERVER_URL, data=data, files=files, headers=headers)
            if response.status_code != 200:
                raise Exception(f"Ошибка сервера: {response.status_code}")
            try:
                response_data = response.json()
            except json.JSONDecodeError:
                raise Exception("Ошибка обработки ответа сервера")
            if not response_data.get('success'):
                raise Exception(f"Ошибка сервера: {response_data.get('message', 'Неизвестная ошибка')}")
            print(f"Фото успешно загружено для пользователя с ID: {response_data.get('user_id')}")
            return True
    except Exception as e:
        raise Exception(f"Ошибка при загрузке на сервер: {str(e)}")
    finally:
        for filename in [orig_filename, analysis_filename]:
            if os.path.exists(filename):
                try: os.remove(filename)
                except: pass
class PlantAnalyzer:
    """Класс для анализа состояния растений по фото"""
    def __init__(self):
        self.font_path = FONT_PATH
        self.color_percentages = {}
        self.detected_diseases = []
        self.detected_pests = []
        self.camera = None
        self.screen_width = 1920
        self.screen_height = 1080
        try:
            from win32api import GetSystemMetrics
            self.screen_width = GetSystemMetrics(0)
            self.screen_height = GetSystemMetrics(1)
        except:
            try:
                import tkinter as tk
                root = tk.Tk()
                self.screen_width = root.winfo_screenwidth()
                self.screen_height = root.winfo_screenheight()
                root.destroy()
            except: pass
    def detect_plant(self):
        hsv = cv2.cvtColor(self.original_image, cv2.COLOR_BGR2HSV)
        self.detection_image = self.original_image.copy()
        total_mask = np.zeros((self.height, self.width), dtype=np.uint8)
        for color_name, color_range in LEAF_COLORS.items():
            mask = cv2.inRange(hsv, color_range["lower"], color_range["upper"])
            kernel = np.ones((3,3), np.uint8)
            mask = cv2.morphologyEx(mask, cv2.MORPH_OPEN, kernel)
            mask = cv2.morphologyEx(mask, cv2.MORPH_CLOSE, kernel)
            total_mask = cv2.bitwise_or(total_mask, mask)
        contours, _ = cv2.findContours(total_mask, cv2.RETR_EXTERNAL, cv2.CHAIN_APPROX_SIMPLE)
        filtered_contours = []
        for contour in contours:
            if cv2.contourArea(contour) > 100:
                filtered_contours.append(contour)
        cv2.drawContours(self.detection_image, filtered_contours, -1, (0, 255, 0), 2)
        self.plant_mask = np.zeros_like(total_mask)
        cv2.drawContours(self.plant_mask, filtered_contours, -1, 255, -1)
        plant_pixels = np.count_nonzero(self.plant_mask)
        if plant_pixels > 0:
            for color_name, color_range in LEAF_COLORS.items():
                mask = cv2.inRange(hsv, color_range["lower"], color_range["upper"])
                color_pixels = cv2.countNonZero(cv2.bitwise_and(mask, self.plant_mask))
                self.color_percentages[color_name] = (color_pixels / plant_pixels) * 100
    def detect_diseases(self):
        self.detected_diseases = []
        if self.color_percentages.get("yellow", 0) > 10:
            self.detected_diseases.append(DISEASES_DB["yellow_leaves"])
        if self.color_percentages.get("brown", 0) > 5:
            self.detected_diseases.append(DISEASES_DB["brown_spots"])
    def detect_pests(self):
        self.detected_pests = []
        if self.color_percentages.get("brown", 0) > 5:
            if self.color_percentages.get("yellow", 0) > 15:
                self.detected_pests.append(PESTS_DB["aphids"])
            elif self.color_percentages.get("brown", 0) > 10:
                self.detected_pests.append(PESTS_DB["thrips"])
    def analyze_health(self):
        self.detect_diseases()
        self.detect_pests()
        status = "нормальное"
        details = []
        recommendations = []
        if self.color_percentages.get("yellow", 0) > 10:
            status = "требует внимания"
            details.append("Обнаружено значительное пожелтение листьев")
            recommendations.append("Проверьте режим полива")
            recommendations.append("Проверьте уровень освещенности")
        if self.color_percentages.get("brown", 0) > 5:
            status = "требует внимания"
            details.append("Обнаружены коричневые участки на листьях")
            recommendations.append("Проверьте на наличие заболеваний")
            recommendations.append("Удалите поврежденные листья")
        for disease in self.detected_diseases:
            details.append(f"{disease['name']}: {disease['description']}")
            recommendations.extend(disease['solutions'])
        for pest in self.detected_pests:
            details.append(f"{pest['name']}: {pest['description']}")
            recommendations.extend(pest['solutions'])
        if not details:
            recommendations.append("Поддерживайте текущий режим ухода")
        return {
            "состояние": status,
            "распределение цветов": "; ".join([f"{LEAF_COLORS[k]['name']}: {v:.1f}%" for k, v in self.color_percentages.items() if v > 1]),
            "детали": "; ".join(details) if details else "отклонений не выявлено",
            "рекомендации": "; ".join(recommendations)
        }
def run_plant_analysis():
    """Выполнить анализ растения по фото"""
    analyzer = PlantAnalyzer()
    try:
        print("\n=== Начало анализа растения ===")
        print(f"API токен: {API_TOKEN}")
        if len(sys.argv) > 1:
            frame = cv2.imread(sys.argv[1])
            if frame is None:
                raise Exception("Ошибка загрузки изображения из файла")
        else:
            frame = take_photo()
        analyzer.original_image = frame.copy()
        analyzer.height, analyzer.width = frame.shape[:2]
        analyzer.detect_plant()
        analysis = analyzer.analyze_health()
        report_text = f"АНАЛИЗ СОСТОЯНИЯ РАСТЕНИЯ\nДата анализа: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n\nСОСТОЯНИЕ: {analysis['состояние']}\n\nРАСПРЕДЕЛЕНИЕ ЦВЕТОВ:\n{analysis['распределение цветов']}\n\nДЕТАЛИ АНАЛИЗА:\n{analysis['детали']}\n\nРЕКОМЕНДАЦИИ:\n{analysis['рекомендации']}\n"
        if upload_to_server(analyzer.original_image, analyzer.detection_image, report_text):
            print("Анализ успешно завершен!")
        else:
            print("Анализ завершен с ошибками!")
        return True
    except Exception as e:
        print(f"Ошибка: {str(e)}")
        return False
def print_status():
    """Выводит информацию о состоянии устройств управления"""
    print("── 📊 Состояние устройств ──────────────")
    if last_led_state is not None:
        print(f"💡 Лампа:   {'✅ включена' if last_led_state == 1 else '❌ выключена'}")
    if last_curtains_state is not None:
        print(f"🪟 Шторы:   {'✅ закрыты' if last_curtains_state == 1 else '❌ открыты'}")
    print("────────────────────────────────────────")
    print()
def get_max_sensor_id():
    """Получает максимальный ID из таблицы sensor_data"""
    try:
        headers = {'X-Auth-Token': API_TOKEN}
        response = requests.get(MAX_ID_API_URL, headers=headers)
        if response.status_code == 200:
            data = response.json()
            if data.get('success') and 'max_id' in data:
                return int(data['max_id'])
            else:
                print(f"{datetime.now().strftime('%Y-%m-%d %H:%M:%S')} - Ошибка получения max_id: {data.get('message', 'Неизвестная ошибка')}")
                return 0
        elif response.status_code == 401:
            print_auth_error()
            return 0
        else:
            print(f"{datetime.now().strftime('%Y-%m-%d %H:%M:%S')} - Сервер вернул код при запросе max_id: {response.status_code}")
            return 0
    except Exception as e:
        print(f"{datetime.now().strftime('%Y-%m-%d %H:%M:%S')} - Ошибка при запросе max_id: {str(e)}")
        return 0
def get_thresholds():
    try:
        headers = {'X-Auth-Token': API_TOKEN}
        response = requests.get(THRESHOLDS_API_URL, headers=headers)
        if response.status_code == 200:
            data = response.json()
            current_time = time.time()
            global last_thresholds_print_time
            if current_time - last_thresholds_print_time >= THRESHOLDS_PRINT_INTERVAL:
                print()
                print(f"📊 Пороговые значения (обновлено: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')})")
                print("────────────────────────────────────────")
                print(f"🌡️ Температура:        {data['temperature']['min']}°C - {data['temperature']['max']}°C")
                print(f"💧 Влажность воздуха:  {data['humidity']['min']}% - {data['humidity']['max']}%")
                print(f"🌱 Влажность почвы:    {data['soil_moisture']['min']}% - {data['soil_moisture']['max']}%")
                print(f"🫧 CO₂:                {data['co2']['min']} ppm - {data['co2']['max']} ppm")
                print("────────────────────────────────────────")
                print_status()
                last_thresholds_print_time = current_time
            return data
        elif response.status_code == 401:
            print_auth_error()
            return None
        return None
    except Exception as e:
        print(f"{datetime.now().strftime('%Y-%m-%d %H:%M:%S')} - Ошибка получения порогов: {str(e)}")
        return None
def get_led_state():
    """Получает текущее состояние лампы с сервера"""
    try:
        headers = {'X-Auth-Token': API_TOKEN}
        response = requests.get(LED_API_URL, headers=headers, timeout=5)
        if response.status_code != 200:
            if response.status_code == 401:
                print_auth_error()
            else:
                print(f"{datetime.now().strftime('%Y-%m-%d %H:%M:%S')} - Ошибка получения состояния лампы: HTTP {response.status_code}")
            return None
        try:
            data = response.json()
            if data.get('success') == True and 'state' in data:
                state = data.get('state')
                return 1 if int(state) == 1 else 0
            else:
                print(f"{datetime.now().strftime('%Y-%m-%d %H:%M:%S')} - Некорректный формат ответа от API: {data}")
                return None
        except json.JSONDecodeError as e:
            print(f"{datetime.now().strftime('%Y-%m-%d %H:%M:%S')} - Ошибка разбора JSON в ответе лампы: {str(e)}")
            print(f"Содержимое ответа: {response.text}")
            return None
    except requests.exceptions.Timeout:
        print(f"{datetime.now().strftime('%Y-%m-%d %H:%M:%S')} - Таймаут при запросе состояния лампы")
        return None
    except requests.exceptions.RequestException as e:
        print(f"{datetime.now().strftime('%Y-%m-%d %H:%M:%S')} - Ошибка сети при запросе состояния лампы: {str(e)}")
        return None
    except Exception as e:
        print(f"{datetime.now().strftime('%Y-%m-%d %H:%M:%S')} - Общая ошибка при получении состояния лампы: {str(e)}")
        return None
def get_curtains_state():
    """Получает текущее состояние штор с сервера"""
    try:
        headers = {'X-Auth-Token': API_TOKEN}
        response = requests.get(CURTAINS_API_URL, headers=headers, timeout=5)
        if response.status_code != 200:
            if response.status_code == 401:
                print_auth_error()
            else:
                print(f"{datetime.now().strftime('%Y-%m-%d %H:%M:%S')} - Ошибка получения состояния штор: HTTP {response.status_code}")
            return None
        try:
            data = response.json()
            if data.get('success') == True and 'state' in data:
                state = data.get('state')
                return 1 if int(state) == 1 else 0
            else:
                print(f"{datetime.now().strftime('%Y-%m-%d %H:%M:%S')} - Некорректный формат ответа от API: {data}")
                return None
        except json.JSONDecodeError as e:
            print(f"{datetime.now().strftime('%Y-%m-%d %H:%M:%S')} - Ошибка разбора JSON в ответе штор: {str(e)}")
            print(f"Содержимое ответа: {response.text}")
            return None
    except requests.exceptions.Timeout:
        print(f"{datetime.now().strftime('%Y-%m-%d %H:%M:%S')} - Таймаут при запросе состояния штор")
        return None
    except requests.exceptions.RequestException as e:
        print(f"{datetime.now().strftime('%Y-%m-%d %H:%M:%S')} - Ошибка сети при запросе состояния штор: {str(e)}")
        return None
    except Exception as e:
        print(f"{datetime.now().strftime('%Y-%m-%d %H:%M:%S')} - Общая ошибка при получении состояния штор: {str(e)}")
        return None 
def send_command(ser, device_type, state):
    try:
        state_value = 1 if state == 1 else 0
        command = f"{device_type}:{state_value}\n"
        if not ser.is_open:
            print(f"❌ Ошибка: последовательный порт закрыт")
            return False
        print(f"📡 Отправляем команду: {command.strip()}")
        ser.write(command.encode())
        if device_type == "LED":
            status_text = "✅ включена" if state_value == 1 else "❌ выключена"
            print(f"💡 Лампа: {status_text}")
            global last_led_state
            last_led_state = state_value
        elif device_type == "CURTAINS":
            status_text = "✅ закрыты" if state_value == 1 else "❌ открыты"
            print(f"🪟 Шторы: {status_text}")
            global last_curtains_state
            last_curtains_state = state_value
        print()
        time.sleep(0.5)  
        if ser.in_waiting:
            response = ser.readline().decode('utf-8', errors='replace').strip()
            if response:
                print(f"🔄 Ответ Arduino: {response}")
        return True
    except serial.SerialException as e:
        print(f"❌ Ошибка последовательного порта: {str(e)}")
        return False
    except Exception as e:
        print(f"❌ Ошибка при отправке команды: {str(e)}")
        return False
def devices_control_thread(ser):
    global last_led_state, last_curtains_state, last_thresholds
    print(f"🧵 Запущен поток управления устройствами")
    print()
    last_led_state = None
    last_curtains_state = None
    current_lamp_state_from_server = -1
    current_curtains_state_from_server = -1
    last_successful_state_check = 0
    check_interval = 5
    error_count = 0
    max_errors = 3
    while True:
        try:
            current_time = time.time()
            if current_time - last_successful_state_check >= check_interval:
                led_state = get_led_state()
                if led_state is not None:
                    error_count = 0
                    last_successful_state_check = current_time
                    current_lamp_state_from_server = led_state
                    if last_led_state is None or last_led_state != current_lamp_state_from_server:
                        print(f"🔔 Обнаружено изменение состояния лампы: {last_led_state if last_led_state is not None else '?'} ➡️ {current_lamp_state_from_server}")
                        if send_command(ser, "LED", current_lamp_state_from_server):
                            last_led_state = current_lamp_state_from_server
                curtains_state = get_curtains_state()
                if curtains_state is not None:
                    error_count = 0
                    last_successful_state_check = current_time
                    current_curtains_state_from_server = curtains_state
                    if last_curtains_state is None or last_curtains_state != current_curtains_state_from_server:
                        print(f"🔔 Обнаружено изменение состояния штор: {last_curtains_state if last_curtains_state is not None else '?'} ➡️ {current_curtains_state_from_server}")
                        if send_command(ser, "CURTAINS", current_curtains_state_from_server):
                            last_curtains_state = current_curtains_state_from_server
            if current_time - last_thresholds_print_time >= THRESHOLDS_PRINT_INTERVAL:
                current_thresholds = get_thresholds()
                if current_thresholds is not None:
                    last_thresholds = current_thresholds
            time.sleep(1)
        except Exception as e:
            print(f"❌ Ошибка в потоке управления устройствами: {str(e)}")
            error_count += 1
            if error_count >= max_errors:
                check_interval = min(30, check_interval * 2)  
                print(f"⚠️ Увеличен интервал проверки до {check_interval} секунд из-за повторяющихся ошибок")
                error_count = 0  
            time.sleep(3)
def save_to_server(user_id=1):
    global last_temperature, last_humidity, last_soil_moisture, last_light_level, last_co2, last_pressure
    global last_led_state, last_curtains_state, last_used_id
    try:
        if last_temperature == 0 or last_humidity == 0:
            return False
        max_id = get_max_sensor_id()
        next_id = max(max_id + 1, last_used_id + 1)
        print(f"{datetime.now().strftime('%Y-%m-%d %H:%M:%S')} - Используем ID {next_id} для новой записи (предыдущий макс. ID: {max_id})")
        post_data = {
            'id': next_id,  
            'user_id': user_id,
            'temperature': float(last_temperature),
            'humidity': float(last_humidity),
            'soil_moisture': float(last_soil_moisture),
            'light_level': float(last_light_level),
            'co2': int(last_co2),
            'pressure': float(last_pressure),
            'lamp_state': int(last_led_state) if last_led_state is not None else 0,
            'curtains_state': int(last_curtains_state) if last_curtains_state is not None else 0
        }
        headers = {
            'Content-Type': 'application/x-www-form-urlencoded',
            'X-Auth-Token': API_TOKEN
        }
        response = requests.post(SENSOR_API_URL, data=post_data, headers=headers)
        if response.status_code == 200:
            try:
                resp_data = response.json()
                if resp_data.get('success'):
                    last_used_id = next_id  
                    current_time = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
                    print()
                    print(f"📅 {current_time}")
                    print("────────────────────────────────────")
                    print(f"🆔 ID записи:              {next_id}")
                    print(f"🌡️ Температура воздуха:    {post_data['temperature']:.1f}°C")
                    print(f"💧 Влажность воздуха:      {post_data['humidity']:.1f}%")
                    print(f"🌱 Влажность почвы:        {post_data['soil_moisture']:.1f}%")
                    print(f"🔆 Уровень освещенности:   {post_data['light_level']:.2f} lx")
                    print(f"🫧 CO₂ уровень:            {post_data['co2']} ppm")
                    print(f"🌬️ Атм. давление:          {post_data['pressure']:.2f} hPa")
                    print(f"💡 Лампа:                  {'включена' if post_data['lamp_state'] == 1 else 'выключена'}")
                    print(f"🪟 Шторы:                  {'закрыты' if post_data['curtains_state'] == 1 else 'открыты'}")
                    print("────────────────────────────────────")
                    return True
                else:
                    print(f"{datetime.now().strftime('%Y-%m-%d %H:%M:%S')} - Ошибка при отправке данных: {resp_data.get('message', 'Неизвестная ошибка')}")
                    return False
            except json.JSONDecodeError:
                print(f"{datetime.now().strftime('%Y-%m-%d %H:%M:%S')} - Ошибка декодирования JSON в ответе")
                return False
        elif response.status_code == 401:
            print_auth_error()
            return False
        else:
            print(f"{datetime.now().strftime('%Y-%m-%d %H:%M:%S')} - Сервер вернул код: {response.status_code}")
            print(f"Ответ: {response.text}")
            return False
    except Exception as e:
        print(f"{datetime.now().strftime('%Y-%m-%d %H:%M:%S')} - Ошибка отправки данных: {str(e)}")
    return False 
def update_sensor_values(line):
    global last_temperature, last_humidity, last_soil_moisture, last_light_level, last_co2, last_pressure
    try:
        temp_match = re.search(r'[Tt]emp(?:erature)?\s*:\s*(\d+\.?\d*)', line)
        if temp_match:
            last_temperature = float(temp_match.group(1))
        humidity_match = re.search(r'[Hh]umidity\s*:\s*(\d+\.?\d*)', line)
        if humidity_match:
            last_humidity = float(humidity_match.group(1))
        soil_match = re.search(r'[Ss]oil\s*moisture\s*:\s*(\d+\.?\d*)', line)
        if soil_match:
            last_soil_moisture = float(soil_match.group(1))
        light_match = re.search(r'[Ll]ight\s*level\s*:\s*(\d+\.?\d*)', line)
        if light_match:
            last_light_level = float(light_match.group(1))
        co2_match = re.search(r'[Cc][Oo]2\s*:\s*(\d+\.?\d*)', line)
        if co2_match:
            last_co2 = float(co2_match.group(1))
        pressure_match = re.search(r'[Pp]ressure\s*:\s*(\d+\.?\d*)', line)
        if pressure_match:
            last_pressure = float(pressure_match.group(1))
        return (last_temperature > 0 and 
                last_humidity > 0 and 
                last_soil_moisture >= 0 and 
                last_light_level >= 0)
    except Exception as e:
        print(f"{datetime.now().strftime('%Y-%m-%d %H:%M:%S')} - Ошибка при обработке данных датчиков: {str(e)}")
        return False
def check_all_sensors_ready():
    global last_temperature, last_humidity, last_soil_moisture, last_light_level
    return (last_temperature > 0 and 
            last_humidity > 0 and 
            last_soil_moisture >= 0 and 
            last_light_level >= 0)
def parse_time(time_str):
    """Преобразует строку времени в секунды"""
    time_units = {
        'ч': 3600, 'h': 3600,  
        'м': 60, 'm': 60,      
        'с': 1, 's': 1         
    }
    pattern = r'(\d+)([чмс]|[hms])'
    matches = re.findall(pattern, time_str.lower())
    if not matches:
        raise ValueError("Неверный формат времени")
    total_seconds = 0
    for number, unit in matches:
        total_seconds += int(number) * time_units[unit]
    return total_seconds
def format_interval(seconds):
    """Форматирует интервал в человекочитаемый вид"""
    hours = seconds // 3600
    minutes = (seconds % 3600) // 60
    seconds = seconds % 60
    parts = []
    if hours > 0:
        parts.append(f"{hours}ч")
    if minutes > 0:
        parts.append(f"{minutes}м")
    if seconds > 0 or not parts:
        parts.append(f"{seconds}с")
    return "".join(parts)
def get_interval_from_user():
    """Запрашивает у пользователя интервал отправки данных"""
    while True:
        print()
        print("⏱️ НАСТРОЙКА ИНТЕРВАЛА ОТПРАВКИ ДАННЫХ")
        print("────────────────────────────────────────")
        print("Введите интервал отправки данных на сервер (часы, минуты, секунды):")
        print("Примеры:")
        print("  1ч       - 1 час")
        print("  30м      - 30 минут")
        print("  45с      - 45 секунд")
        print("  1ч30м    - 1 час 30 минут")
        print("  2м30с    - 2 минуты 30 секунд")
        print("────────────────────────────────────────")
        try:
            interval_str = input("Интервал: ").strip()
            interval_seconds = parse_time(interval_str)
            print(f"✅ Установлен интервал отправки данных: {format_interval(interval_seconds)}")
            print()
            return interval_seconds
        except ValueError as e:
            print(f"❌ Ошибка: {str(e)}")
            print("Попробуйте еще раз")
            print()
def get_photo_interval_from_user():
    """Запрашивает у пользователя интервал выполнения фотографий"""
    while True:
        print()
        print("📸 НАСТРОЙКА ИНТЕРВАЛА ФОТОГРАФИРОВАНИЯ")
        print("────────────────────────────────────────")
        print("Введите интервал создания фотографий (часы, минуты, секунды):")
        print("Примеры:")
        print("  1ч       - 1 час")
        print("  30м      - 30 минут")
        print("  45с      - 45 секунд")
        print("  1ч30м    - 1 час 30 минут")
        print("  2м30с    - 2 минуты 30 секунд")
        print("────────────────────────────────────────")
        try:
            interval_str = input("Интервал: ").strip()
            interval_seconds = parse_time(interval_str)
            print(f"✅ Установлен интервал фотографирования: {format_interval(interval_seconds)}")
            print()
            return interval_seconds
        except ValueError as e:
            print(f"❌ Ошибка: {str(e)}")
            print("Попробуйте еще раз")
            print()
def photo_thread_function(photo_interval):
    """Функция для потока, выполняющего периодическое фотографирование"""
    print(f"🧵 Запущен поток периодического фотографирования (интервал: {format_interval(photo_interval)})")
    last_photo_time = 0
    while True:
        try:
            current_time = time.time()
            if current_time - last_photo_time >= photo_interval:
                print("\n=== Выполнение периодического фотографирования ===")
                analyzer = PlantAnalyzer()
                try:
                    frame = take_photo()
                    analyzer.original_image = frame.copy()
                    analyzer.height, analyzer.width = frame.shape[:2]
                    analyzer.detect_plant()
                    analysis = analyzer.analyze_health()
                    report_text = f"АНАЛИЗ СОСТОЯНИЯ РАСТЕНИЯ\nДата анализа: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n\nСОСТОЯНИЕ: {analysis['состояние']}\n\nРАСПРЕДЕЛЕНИЕ ЦВЕТОВ:\n{analysis['распределение цветов']}\n\nДЕТАЛИ АНАЛИЗА:\n{analysis['детали']}\n\nРЕКОМЕНДАЦИИ:\n{analysis['рекомендации']}\n"
                    if upload_to_server(analyzer.original_image, analyzer.detection_image, report_text):
                        print(f"✅ Периодическая фотография успешно загружена ({datetime.now().strftime('%Y-%m-%d %H:%M:%S')})")
                        last_photo_time = current_time
                    else:
                        print(f"❌ Ошибка при загрузке периодической фотографии")
                except Exception as e:
                    print(f"❌ Ошибка при выполнении периодического фотографирования: {str(e)}")
                    last_photo_time = current_time
            time.sleep(min(60, photo_interval / 10))  
        except Exception as e:
            print(f"❌ Ошибка в потоке фотографирования: {str(e)}")
            time.sleep(10)  
def run_sensor_monitoring():
    """Запустить мониторинг датчиков"""
    global last_temperature, last_humidity, last_soil_moisture, last_light_level, last_co2, last_pressure
    global last_led_state, last_curtains_state, last_used_id
    last_temperature = -1
    last_humidity = -1
    last_soil_moisture = -1
    last_light_level = -1
    last_co2 = 400
    last_pressure = 1013.25
    last_led_state = None
    last_curtains_state = None
    last_used_id = get_max_sensor_id()
    print(f"🔢 Максимальный ID в базе данных: {last_used_id}")
    try:
        sensor_interval = get_interval_from_user()
        photo_interval = get_photo_interval_from_user()
        print(f"🔌 Подключение к Arduino на порту {SERIAL_PORT}...")
        try:
            ser = serial.Serial(SERIAL_PORT, BAUD_RATE, timeout=1)
            print(f"✅ Подключено к Arduino на порту {SERIAL_PORT}")
        except serial.SerialException as e:
            print(f"❌ Ошибка подключения к Arduino: {str(e)}")
            print("   Проверьте:")
            print("   1. Подключен ли Arduino к компьютеру")
            print("   2. Правильный ли COM-порт указан в настройках")
            print("   3. Не занят ли порт другой программой")
            return
        print(f"📡 Ожидание данных с датчиков...")
        devices_thread = threading.Thread(target=devices_control_thread, args=(ser,), daemon=True)
        devices_thread.start()
        photo_thread = threading.Thread(target=photo_thread_function, args=(photo_interval,), daemon=True)
        photo_thread.start()
        last_send_time = 0
        first_data_collected = False
        data_ready = False
        while True:
            try:
                if ser.in_waiting:
                    line = ser.readline().decode('utf-8', errors='replace').strip()
                    if not line:
                        continue
                    if line.startswith("LED:") or line.startswith("CURTAINS:"):
                        continue
                    all_data_received = update_sensor_values(line)
                    if not first_data_collected:
                        if check_all_sensors_ready():
                            first_data_collected = True
                            data_ready = True
                            print(f"✅ Получены первые данные со всех датчиков")
                    else:
                        if all_data_received:
                            data_ready = True
                    current_time = time.time()
                    if data_ready and (current_time - last_send_time >= sensor_interval):
                        if save_to_server():
                            last_send_time = current_time
                            data_ready = False
                time.sleep(0.1)
            except serial.SerialException as e:
                print(f"❌ Ошибка последовательного порта: {str(e)}")
                time.sleep(1)
            except Exception as e:
                print(f"❌ Ошибка в основном цикле: {str(e)}")
                time.sleep(1)
    except KeyboardInterrupt:
        print()
        print("👋 Программа остановлена пользователем")
    except Exception as e:
        print()
        print(f"⛔ Критическая ошибка: {str(e)}")
    finally:
        if 'ser' in locals() and ser.is_open:
            ser.close()
            print(f"🔌 Соединение с Arduino закрыто")
def main():
    """Основная функция программы"""
    global API_TOKEN
    API_TOKEN = get_api_token()
    print("\n==== УПРАВЛЕНИЕ УМНОЙ ТЕПЛИЦЕЙ ====")
    print("API токен:", API_TOKEN)
    print("\n1. Выполнение первичного фото и анализа растения...")
    run_plant_analysis()
    print("\n2. Запуск мониторинга датчиков и периодического фотографирования...")
    run_sensor_monitoring()
if __name__ == "__main__":
    main() 