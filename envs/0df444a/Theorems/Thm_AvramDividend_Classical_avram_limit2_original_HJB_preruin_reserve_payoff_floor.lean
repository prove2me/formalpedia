-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_original_HJB_preruin_reserve_payoff_floor
-- name    : AvramDividend.Classical.avram_limit2_original_HJB_preruin_reserve_payoff_floor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T21:37:58.094535+00:00
-- url     : https://prove2.me/theorems/228d9ebf-0eb4-49b3-88be-9112e1dfe0f1
-- title:
--   Original physical pre-ruin HJB payoff dominates the reserve in both variation branches
-- statement:
--   The original maximum HJB identity, branch-specific BV C1/UBV C2 regularity, and physical admissible risk-process range imply that at every time strictly before ruin, the risk reserve is bounded above by its candidate payoff, including the cap boundary and C=top.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_HJB_all_variation_payoff_above_reserve
import Theorems.Thm_AvramDividend_Classical_capped_riskProcess_range_before_ruin_including_zero
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_limit2_original_HJB_preruin_reserve_payoff_floor
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
    ∀ (x : ℝ), 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ (D : ℝ≥0 → Ω → ℝ), IsAdmissibleLe X x C D →
      ∀ ω (t : ℝ≥0),
        (t : ℝ≥0∞) < ruinTime X x D ω →
        riskProcess X x D t ω ≤ w (riskProcess X x D t ω) := by sorry
