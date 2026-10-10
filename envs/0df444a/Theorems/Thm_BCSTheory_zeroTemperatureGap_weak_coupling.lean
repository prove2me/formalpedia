-- Prove2me | Theorems.Thm_BCSTheory_zeroTemperatureGap_weak_coupling
-- name    : BCSTheory.zeroTemperatureGap_weak_coupling
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:23:42.879995+00:00
-- url     : https://prove2.me/theorems/be832b61-a1ba-440b-a77e-082c21750429
-- title:
--   Weak coupling: $\Delta(0) \approx 2\hbar\omega_D\, e^{-1/V_0 Z(E_F)}$
-- statement:
--   For fixed $\hbar\omega_D>0$, as the coupling $\lambda = V_0Z(E_F) \to 0^+$, $$\frac{\Delta(0)}{2\hbar\omega_D\, e^{-1/\lambda}} \to 1.$$
-- source:
--   Wikipedia (de), Artikel „BCS-Theorie“ (PDF-Ausdruck vom 05.10.2026), Abschnitt „Erfolge der BCS-Theorie“, Unterabschnitt „Existenz einer Energielücke“, zweite Formel (Näherung für $V_0 Z(E_F) \ll 1$).

import Mathlib
import Definitions.Def_BCSTheory_GapEquation
open Filter Topology

namespace BCSTheory

theorem zeroTemperatureGap_weak_coupling (hbarOmegaD : ℝ) (hω : 0 < hbarOmegaD) :
    Tendsto (fun coupling : ℝ =>
        zeroTemperatureGap hbarOmegaD coupling / (2 * hbarOmegaD * Real.exp (-1 / coupling)))
      (𝓝[>] 0) (𝓝 1) := by sorry

end BCSTheory
