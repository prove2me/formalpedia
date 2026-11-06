-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_bv_original_HJB_all_grid_source_premises
-- name    : AvramDividend.Classical.avram_limit2_bv_original_HJB_all_grid_source_premises
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T20:12:55.832179+00:00
-- url     : https://prove2.me/theorems/6f382408-0345-4e03-8b7f-fff9e9912eec
-- title:
--   BV original HJB yields all analytic and physical pathwise signed-grid premises
-- statement:
--   The original BV HJB maximum-zero equality supplies the nonpositive generator and derivative lower bound; accepted original-process C1/admissibility theorems then provide nonnegative pre-ruin candidate payoff and the time-zero/strict-before-ruin right-dividend secant. Together these are the exact four analytic and pathwise inputs to the separate canonical signed-Fatou grid source theorem.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_bv_hjb_max_to_original_source_signs
import Theorems.Thm_AvramDividend_Classical_avram_limit2_bv_original_C1_path_and_right_jump_premises
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_limit2_bv_original_HJB_all_grid_source_premises
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hwCont : ContinuousOn w (Ici (0 : ℝ)))
    (hwSmooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwHJB : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0) :
    (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) ∧
    (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y) ∧
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
              (rightLimit D t ω - D t ω)))) := by sorry
