-- Prove2me | Theorems.Thm_BoltzmannConstant_thermal_voltage_at_300K
-- name    : BoltzmannConstant.thermal_voltage_at_300K
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T15:19:53.828743+00:00
-- url     : https://prove2.me/theorems/bfbd236d-87b1-4ece-8b6d-1bdff54c6b1f
-- title:
--   Thermal voltage at 300 K is approximately 25.85 mV
-- statement:
--   In semiconductors the Shockley diode equation depends on the thermal voltage $V_T = k_BT/q$, where $q$ is the elementary charge. At room temperature $T = 300\ \mathrm{K}$ its value is approximately $25.85\ \mathrm{mV}$; the claim makes this precise by bounding the deviation from $0.02585\ \mathrm{V}$ by $10^{-5}\ \mathrm{V}$.
-- source:
--   Wikipedia, "Boltzmann constant" (uploaded PDF), https://en.wikipedia.org/wiki/Boltzmann_constant, section "Thermal voltage" ($V_T = kT/q$; at 300 K, $V_T \approx 25.85$ mV)

import Mathlib
import Definitions.Def_boltzmann_si_basics

namespace BoltzmannConstant

theorem thermal_voltage_at_300K : |thermalVoltage 300 - 0.02585| < 1e-5 := by sorry

end BoltzmannConstant
