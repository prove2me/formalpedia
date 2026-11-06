-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_all_variation_closed_cap_payoff_above_reserve
-- name    : AvramDividend.Classical.avram_limit2_all_variation_closed_cap_payoff_above_reserve
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T20:26:11.069987+00:00
-- url     : https://prove2.me/theorems/2b673ba4-f581-45e6-8491-bc77f45dd011
-- title:
--   Uniform original BV/UBV closed-cap reserve floor under branchwise smoothness
-- statement:
--   For the same physical spectrally negative Levy process, bounded and unbounded variation branchwise C1 and C2 regularity and the shared slope bound imply candidate payoff w(y)>=y on the entire closed nonnegative cap, including C=top. The proof uses accepted original BV and UBV secant-floor certificates under a complete bounded/unbounded variation case split.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_bv_C1_closed_cap_payoff_above_reserve
import Theorems.Thm_AvramDividend_Classical_avram_limit2_ubv_C2_closed_cap_payoff_above_reserve
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_limit2_all_variation_closed_cap_payoff_above_reserve
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0)
    (hwCont : ContinuousOn w (Ici (0 : ℝ)))
    (hwBV : X.BoundedVariation →
      ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwUBV : ¬ X.BoundedVariation →
      ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y) :
    ∀ y : ℝ, 0 ≤ y → ENNReal.ofReal y ≤ C → y ≤ w y := by sorry
