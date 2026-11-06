-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_original_HJB_allvar_source_signs_payoff_jump
-- name    : AvramDividend.Classical.avram_limit2_original_HJB_allvar_source_signs_payoff_jump
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T21:50:10.569062+00:00
-- url     : https://prove2.me/theorems/48654fa7-fedb-44d1-b0ac-3305966f9e8d
-- title:
--   Original HJB both-variation generator signs and physical payoff jump certificate
-- statement:
--   In the original physical classical dividend model, the common maximum HJB equation and BV C1/UBV C2 smoothness imply generator and slope inequalities, pre-ruin nonnegative payoff, the exact initial-or-strict-pre-ruin right-dividend secant, and a quantitative reserve-to-payoff bound, uniformly through cap contact.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_bv_hjb_max_to_original_source_signs
import Theorems.Thm_AvramDividend_Classical_avram_limit2_bv_original_C1_path_and_right_jump_premises
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_HJB_all_variation_payoff_above_reserve
import Theorems.Thm_AvramDividend_Classical_capped_riskProcess_range_before_ruin_including_zero
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_limit2_original_HJB_allvar_source_signs_payoff_jump
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
    (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) ∧
    (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) ∧
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ (D : ℝ≥0 → Ω → ℝ), IsAdmissibleLe X x C D →
      (∀ ω (t : ℝ≥0), 0 < t →
        (t : ℝ≥0∞) < ruinTime X x D ω →
        0 ≤ w (riskProcess X x D t ω)) ∧
      (∀ ω (t : ℝ≥0),
        (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
        rightLimit D t ω - D t ω ≤
          w (riskProcess X x D t ω) -
            w (riskProcess X x D t ω -
              (rightLimit D t ω - D t ω)))) ∧
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ (D : ℝ≥0 → Ω → ℝ), IsAdmissibleLe X x C D →
      ∀ ω (t : ℝ≥0),
        (t : ℝ≥0∞) < ruinTime X x D ω →
        riskProcess X x D t ω ≤ w (riskProcess X x D t ω)) := by sorry
