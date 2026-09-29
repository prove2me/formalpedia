-- Prove2me | Theorems.Thm_BoltzmannConstant_rms_speed_ratio
-- name    : BoltzmannConstant.rms_speed_ratio
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T14:14:12.6946+00:00
-- url     : https://prove2.me/theorems/5688b3f9-c6f8-4a6c-8f58-dedb3186cc39
-- title:
--   $v_{\mathrm{rms}}$ is inversely proportional to $\sqrt{m}$
-- statement:
--   The thermal energy determines the root-mean-square speed of the atoms, $v_{\mathrm{rms}} = \sqrt{3k_BT/m}$, which is therefore inversely proportional to the square root of the atomic mass. Stated as a ratio: for two monatomic gases of masses $m_1, m_2 > 0$ at the same temperature $T > 0$, $$\frac{v_{\mathrm{rms}}(m_1)}{v_{\mathrm{rms}}(m_2)} = \sqrt{\frac{m_2}{m_1}}.$$ This is what makes the room-temperature figures range from about $1370\ \mathrm{m/s}$ for helium down to about $240\ \mathrm{m/s}$ for xenon.
-- source:
--   Wikipedia, "Boltzmann constant" (uploaded PDF), https://en.wikipedia.org/wiki/Boltzmann_constant, section "Role in the equipartition of energy" (root-mean-square speed inversely proportional to the square root of the atomic mass)

import Mathlib
import Definitions.Def_boltzmann_si_basics

namespace BoltzmannConstant

theorem rms_speed_ratio (T m₁ m₂ : ℝ) (hT : 0 < T) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) :
    Real.sqrt (3 * kB * T / m₁) / Real.sqrt (3 * kB * T / m₂) = Real.sqrt (m₂ / m₁) := by sorry

end BoltzmannConstant
