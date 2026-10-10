-- Prove2me | Theorems.Thm_BCSTheory_criticalTemperature_weak_coupling
-- name    : BCSTheory.criticalTemperature_weak_coupling
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:26:26.994014+00:00
-- url     : https://prove2.me/theorems/348b9376-f61a-4ad8-8475-b3c536fe1cd6
-- title:
--   Weak coupling: $k_BT_c \approx 1.14\,\hbar\omega_D\,e^{-1/V_0Z(E_F)}$
-- statement:
--   For fixed $k_B>0$ and $\hbar\omega_D>0$, as $\lambda=V_0Z(E_F)\to0^+$, $$\frac{k_BT_c}{\hbar\omega_D\,e^{-1/\lambda}} \to \frac{2e^{\gamma}}{\pi} = 1.1338\ldots,$$ where $\gamma$ is the Euler–Mascheroni constant.
-- source:
--   Wikipedia (de), Artikel „BCS-Theorie“ (PDF-Ausdruck vom 05.10.2026), Abschnitt „Erfolge der BCS-Theorie“, Unterabschnitt „Existenz einer Energielücke“, Formel $k_BT_c = 1{,}14\,\hbar\omega_D e^{-1/V_0Z(E_F)}$ (exakte Konstante $2e^\gamma/\pi$ folgt aus $\Delta(0) = 2\hbar\omega_D e^{-1/V_0Z(E_F)} = (\pi/e^\gamma) k_BT_c$).

import Mathlib
import Definitions.Def_BCSTheory_GapEquation
open Filter Topology

namespace BCSTheory

theorem criticalTemperature_weak_coupling (kB hbarOmegaD : ℝ) (hkB : 0 < kB)
    (hω : 0 < hbarOmegaD) :
    Tendsto (fun coupling : ℝ =>
        kB * criticalTemperature kB hbarOmegaD coupling /
          (hbarOmegaD * Real.exp (-1 / coupling)))
      (𝓝[>] 0) (𝓝 (2 * Real.exp Real.eulerMascheroniConstant / Real.pi)) := by sorry

end BCSTheory
