#!/bin/sh
# EmuELEC Web Manager 安装/启动脚本（systemd）
# Install/enable the webmanager as a systemd user-config unit.
# EmuELEC has no /etc/systemd/system on the read-only root, but
# /storage/.config/system.d is on systemd's unit path.
DIR=/storage/.config/webmanager
UNITDIR=/storage/.config/system.d
UNIT=$UNITDIR/webmanager.service

mkdir -p "$UNITDIR"
cat > "$UNIT" <<'EOF'
[Unit]
Description=EmuELEC Web Manager
After=network-online.target
Wants=network-online.target

[Service]
Type=simple
WorkingDirectory=/storage/.config/webmanager
ExecStart=/usr/bin/python3 /storage/.config/webmanager/server.py
Restart=always
RestartSec=3
StandardOutput=append:/storage/.config/webmanager/server.log
StandardError=append:/storage/.config/webmanager/server.log

[Install]
WantedBy=emuelec.target
EOF

systemctl daemon-reload
systemctl enable webmanager.service 2>/dev/null || {
  mkdir -p "$UNITDIR/emuelec.target.wants"
  ln -sf "$UNIT" "$UNITDIR/emuelec.target.wants/webmanager.service"
}
# --no-block: when this script runs from the web UI self-update, the unit we
# restart is ourselves; blocking would kill the restart call mid-flight.
systemctl restart --no-block webmanager.service
sleep 1
IP=$(ip -4 addr show | grep -oP 'inet \K[0-9.]+' | grep -v '^127\.' | head -1)
echo "EmuELEC Web Manager 已启动: http://$IP/"
