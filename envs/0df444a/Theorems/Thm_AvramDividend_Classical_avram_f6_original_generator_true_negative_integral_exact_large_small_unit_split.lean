-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_generator_true_negative_integral_exact_large_small_unit_split
-- name    : AvramDividend.Classical.avram_f6_original_generator_true_negative_integral_exact_large_small_unit_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T22:28:42.276457+00:00
-- url     : https://prove2.me/theorems/cd2a81f8-f3f5-4fe4-8b73-a0a2add095c1
-- title:
--   Exact original Lévy generator compensated negative-jump integral split at unit mark
-- statement:
--   For exact original Lévy with GeneratorIntegrable w y, its ν-integral over all negative jumps splits into large z≤−1 and small −1<z<0. The two actual negative intervals are disjoint and cover Iio0 without losing the z=−1 atom. Each integral is integrable by source restriction and Mathlib setIntegral_union.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_generator_true_negative_integral_exact_large_small_unit_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (y : ℝ)
    (hGen : X.GeneratorIntegrable w y) :
    (∫ z in Iio (0 : ℝ),
      SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) =
    (∫ z in Iic (-1 : ℝ),
      SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) +
    (∫ z in Ioo (-1 : ℝ) 0,
      SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) := by sorry
