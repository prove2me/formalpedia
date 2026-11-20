-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_finite_activity_generator_negative_jump_integral_floor
-- name    : AvramDividend.Classical.avram_f6_original_finite_activity_generator_negative_jump_integral_floor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T20:46:48.463055+00:00
-- url     : https://prove2.me/theorems/fd8514d5-e2db-47fc-b0ce-c2a2476e78c8
-- title:
--   True finite-activity negative-jump generator integral bounded below by actual jump rate times minus w
-- statement:
--   For finite actual source ν(-∞,0), true generator integrability and w≥0 with derivative≥0, exact negative-jump integral is ≥−(ν(-∞,0))·w(y). This follows from the genuine pointwise source jump-integrand lower bound and monotonicity of integral with finite measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_finite_activity_generator_negative_jump_integral_floor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hνFin : X.ν (Iio (0 : ℝ)) < ⊤)
    (w : ℝ → ℝ) (hwpos : ∀ u : ℝ, 0 ≤ w u)
    (y : ℝ) (hderiv : 0 ≤ deriv w y)
    (hGen : X.GeneratorIntegrable w y) :
    -(X.ν (Iio (0 : ℝ))).toReal * w y ≤
      ∫ z in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν := by sorry
