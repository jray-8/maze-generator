@echo off

if not exist resources (
    mkdir resources
)

REM Build with PyInstaller
pyinstaller --onefile --noconsole --icon=resources\maze_icon.ico maze_generator.py

REM Move the .exe to 'releases'
move /Y dist\maze_generator.exe releases\

REM Clean up build mess
rmdir /S /Q build
rmdir /S /Q dist
del /Q maze_generator.spec

echo Build complete! New EXE in releases.
pause
