-- Prove2me | Theorems.Thm_BCSTheory_specific_heat_jump_weak_coupling
-- name    : BCSTheory.specific_heat_jump_weak_coupling
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:30:33.78676+00:00
-- url     : https://prove2.me/theorems/d477901a-1a99-439d-a49d-2e941d6aab29
-- title:
--   Specific-heat jump at $T_c$: $(C_{es}-C_{en})/C_{en} \approx 1.43$
-- statement:
--   For fixed $k_B,\hbar\omega_D>0$: for every coupling $\lambda>0$ the left derivative $D(\lambda) = \frac{d\Delta^2}{dT}\big|_{T_c^-}$ exists, and the BCS specific-heat jump $$\frac{C_{es}-C_{en}}{C_{en}} = \frac{1}{\frac{\pi^2}{3}k_B^2T_cZ}\cdot\frac{Z}{2}\Bigl(-\frac{d\Delta^2}{dT}\Bigr)\Big|_{T_c} = \frac{-D(\lambda)}{\frac{2\pi^2}{3}k_B^2T_c}$$ tends to $\frac{12}{7\zeta(3)} = 1.426\ldots$ as $\lambda\to0^+$.
-- source:
--   Wikipedia (de), Artikel „BCS-Theorie“ (PDF-Ausdruck vom 05.10.2026), Abschnitt „Erfolge der BCS-Theorie“, Unterabschnitt „Wärmekapazitätssprung bei der Sprungtemperatur“, Sprungformel $\approx 1{,}43$.

import Mathlib
import Definitions.Def_BCSTheory_GapEquation
open Filter Topology

namespace BCSTheory

theorem specific_heat_jump_weak_coupling (kB hbarOmegaD : ℝ) (hkB : 0 < kB)
    (hω : 0 < hbarOmegaD) :
    ∃ D : ℝ → ℝ,
      (∀ coupling : ℝ, 0 < coupling →
        HasDerivWithinAt (fun T : ℝ => gap kB hbarOmegaD coupling T ^ 2) (D coupling)
          (Set.Iic (criticalTemperature kB hbarOmegaD coupling))
          (criticalTemperature kB hbarOmegaD coupling)) ∧
      Tendsto (fun coupling : ℝ => -D coupling /
          (2 * Real.pi ^ 2 / 3 * kB ^ 2 * criticalTemperature kB hbarOmegaD coupling))
        (𝓝[>] 0) (𝓝 (12 / (7 * (riemannZeta 3).re))) := by sorry

end BCSTheory
