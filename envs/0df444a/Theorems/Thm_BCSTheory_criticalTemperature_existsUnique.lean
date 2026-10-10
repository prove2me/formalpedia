-- Prove2me | Theorems.Thm_BCSTheory_criticalTemperature_existsUnique
-- name    : BCSTheory.criticalTemperature_existsUnique
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:25:12.135575+00:00
-- url     : https://prove2.me/theorems/39968ffc-e94a-468f-8a07-89e2e086579f
-- title:
--   The critical-temperature equation has a unique solution $T_c>0$
-- statement:
--   For $k_B>0$, $\hbar\omega_D>0$ and $\lambda=V_0Z(E_F)>0$ there is exactly one $T>0$ with $$\frac{1}{\lambda} = \int_0^{\hbar\omega_D}\frac{d\eta}{\eta}\tanh\frac{\eta}{2k_BT};$$ this is the critical temperature $T_c$.
-- source:
--   Wikipedia (de), Artikel „BCS-Theorie“ (PDF-Ausdruck vom 05.10.2026), Abschnitt „Erfolge der BCS-Theorie“, Unterabschnitt „Existenz einer Energielücke“, Gleichung bei der Übergangstemperatur $T_c$ ($\Delta(T_c)=0$).

import Mathlib
import Definitions.Def_BCSTheory_GapEquation
open Filter Topology

namespace BCSTheory

theorem criticalTemperature_existsUnique (kB hbarOmegaD coupling : ℝ) (hkB : 0 < kB)
    (hω : 0 < hbarOmegaD) (hc : 0 < coupling) :
    ∃! T : ℝ, 0 < T ∧ gapIntegral kB hbarOmegaD 0 T = 1 / coupling := by sorry

end BCSTheory
