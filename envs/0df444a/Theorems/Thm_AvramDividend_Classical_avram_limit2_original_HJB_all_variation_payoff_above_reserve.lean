-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_original_HJB_all_variation_payoff_above_reserve
-- name    : AvramDividend.Classical.avram_limit2_original_HJB_all_variation_payoff_above_reserve
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T20:27:05.143407+00:00
-- url     : https://prove2.me/theorems/018af645-bee8-4f45-9e34-d8a154472db0
-- title:
--   Original maximum-HJB uniform BV/UBV closed-cap candidate reserve floor
-- statement:
--   Under the exact original maximum HJB equality, its derivative lower bound and the physical BV C1/UBV C2 branchwise smoothness entail y<=w(y) for all capped nonnegative reserves, including cap equality and C=top. This uniform deterministic bound requires neither stochastic source-grid assumptions nor an infinite-horizon limit.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_bv_hjb_max_to_original_source_signs
import Theorems.Thm_AvramDividend_Classical_avram_limit2_bv_C1_closed_cap_payoff_above_reserve
import Theorems.Thm_AvramDividend_Classical_avram_limit2_ubv_C2_closed_cap_payoff_above_reserve
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_limit2_original_HJB_all_variation_payoff_above_reserve
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0)
    (hwCont : ContinuousOn w (Ici (0 : ℝ)))
    (hwBV : X.BoundedVariation →
      ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwUBV : ¬ X.BoundedVariation →
      ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwHJB : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0) :
    ∀ y : ℝ, 0 ≤ y → ENNReal.ofReal y ≤ C → y ≤ w y := by sorry
