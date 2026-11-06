-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_bv_original_C1_path_and_right_jump_premises
-- name    : AvramDividend.Classical.avram_limit2_bv_original_C1_path_and_right_jump_premises
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T20:06:48.357428+00:00
-- url     : https://prove2.me/theorems/7dcfd126-fda0-4c49-b42f-86205a127d81
-- title:
--   Original BV C1 pathwise payoff and zero-or-pre-ruin right-dividend jump premises
-- statement:
--   For every original admissible capped dividend strategy, C1 interior regularity, the slope-one generator regime and continuity at zero entail nonnegative candidate payoff at every positive strictly pre-ruin reserve and a right-payment secant bound including time zero. Both are exact side premises of the canonical signed-Fatou source theorem.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_initial_value_nonnegative
import Theorems.Thm_AvramDividend_Classical_capped_riskProcess_range_before_ruin_including_zero
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_zero_or_strict_preruin_C1_canonical_hjump_without_standing
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_limit2_bv_original_C1_path_and_right_jump_premises
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hwCont : ContinuousOn w (Ici (0 : ℝ))) (hw0 : 0 ≤ w 0)
    (hwSmooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y) :
    ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ (D : ℝ≥0 → Ω → ℝ), IsAdmissibleLe X x C D →
      (∀ ω (t : ℝ≥0), 0 < t →
        (t : ℝ≥0∞) < ruinTime X x D ω →
        0 ≤ w (riskProcess X x D t ω)) ∧
      (∀ ω (t : ℝ≥0),
        (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
        rightLimit D t ω - D t ω ≤
          w (riskProcess X x D t ω) -
            w (riskProcess X x D t ω -
              (rightLimit D t ω - D t ω))) := by sorry
