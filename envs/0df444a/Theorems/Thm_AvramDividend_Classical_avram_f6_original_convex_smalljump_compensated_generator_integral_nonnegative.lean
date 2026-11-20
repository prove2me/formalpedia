-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_convex_smalljump_compensated_generator_integral_nonnegative
-- name    : AvramDividend.Classical.avram_f6_original_convex_smalljump_compensated_generator_integral_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T22:35:39.904593+00:00
-- url     : https://prove2.me/theorems/dcb1877d-f390-4319-8f84-19f7425d7982
-- title:
--   True Lévy compensated small negative jump generator integral is nonnegative for differentiable convex candidate
-- statement:
--   For exact original Lévy negative mark measure ν and a globally convex differentiable w, the real compensated small negative-jump generator integral over (-1,0) is nonnegative. Uses source pointwise convex Taylor nonnegative lemma and integral_nonneg_of_ae over actual restricted original ν.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_convex_smalljump_compensated_generator_integral_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hConvex : ConvexOn ℝ Set.univ w)
    (y : ℝ) (hDiff : DifferentiableAt ℝ w y) :
    0 ≤ ∫ z in Ioo (-1 : ℝ) 0,
      SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν := by sorry
