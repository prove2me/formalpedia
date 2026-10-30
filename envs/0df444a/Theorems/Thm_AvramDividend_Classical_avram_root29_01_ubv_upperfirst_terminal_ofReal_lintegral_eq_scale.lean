-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_ubv_upperfirst_terminal_ofReal_lintegral_eq_scale
-- name    : AvramDividend.Classical.avram_root29_01_ubv_upperfirst_terminal_ofReal_lintegral_eq_scale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T17:27:10.74798+00:00
-- url     : https://prove2.me/theorems/b7631a5c-f6c4-4265-aec8-632ed6c9bd0b
-- title:
--   Exact original unbounded-variation upper-first q-scale terminal lower integral
-- statement:
--   For an actual unbounded-variation spectrally negative Levy process, positive q and 0<=x<=a with a>0, show the nonnegative extended integral of the strict upper-first discounted q-scale terminal reward equals ENNReal.ofReal(W(x)). Apply the proved genuine real terminal expectation and nonnegative true two-branch horizon payoff, with the exact real-to-ENNReal integral bridge; no Standing or Open two-sided exit statement.
-- source:
--   True original-P UBV upper-first terminal Bochner expectation, source-independent upper split positivity, pinned Mathlib ofReal_integral_eq_lintegral_ofReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_01_ubv_upperfirst_terminal_ofReal_lintegral_eq_scale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    (∫⁻ ω, ENNReal.ofReal
      (if twoSidedExitUpTime X (a-x) ω <
          twoSidedExitDownTime X (-x) ω then
        Real.exp (-(q * ((twoSidedExitUpTime X (a-x) ω).toNNReal : ℝ))) *
          W (x + X.X (twoSidedExitUpTime X (a-x) ω).toNNReal ω)
      else 0) ∂P) = ENNReal.ofReal (W x) := by sorry
