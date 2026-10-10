-- Prove2me | Theorems.Thm_BCSTheory_gapIntegralZeroTemp_eq_arsinh
-- name    : BCSTheory.gapIntegralZeroTemp_eq_arsinh
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:22:35.673105+00:00
-- url     : https://prove2.me/theorems/6eb48ae4-01e6-4583-aa4d-bfb4ac6713e9
-- title:
--   Zero-temperature gap integral equals $\operatorname{arsinh}(\hbar\omega_D/\Delta)$
-- statement:
--   For every Debye energy $\hbar\omega_D > 0$ and every $\Delta > 0$,
--   $$\int_0^{\hbar\omega_D} \frac{d\eta}{\sqrt{\eta^2+\Delta^2}} = \operatorname{arsinh}\frac{\hbar\omega_D}{\Delta}.$$
-- source:
--   Wikipedia (de), Artikel „BCS-Theorie“ (PDF-Ausdruck vom 05.10.2026), Abschnitt „Erfolge der BCS-Theorie“, Unterabschnitt „Existenz einer Energielücke“, erste Formel (T = 0).

import Mathlib
import Definitions.Def_BCSTheory_GapEquation
open Filter Topology

namespace BCSTheory

theorem gapIntegralZeroTemp_eq_arsinh (hbarOmegaD Δ : ℝ) (hω : 0 < hbarOmegaD)
    (hΔ : 0 < Δ) :
    gapIntegralZeroTemp hbarOmegaD Δ = Real.arsinh (hbarOmegaD / Δ) := by sorry

end BCSTheory
