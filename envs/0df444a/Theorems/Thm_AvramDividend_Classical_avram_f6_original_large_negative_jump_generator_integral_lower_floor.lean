-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_large_negative_jump_generator_integral_lower_floor
-- name    : AvramDividend.Classical.avram_f6_original_large_negative_jump_generator_integral_lower_floor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T22:29:16.003183+00:00
-- url     : https://prove2.me/theorems/406fa4cc-ff2a-4be5-b16f-114ea09e5435
-- title:
--   Original infinite-activity-compatible large negative jump generator integral lower bound
-- statement:
--   For every actual spectrally negative Lévy X, with possibly infinite total negative-jump activity, true ν has finite mass on z≤−1. Given GeneratorIntegrable w y, globally nonnegative w and nonnegative deriv w y, source large-mark generator integral satisfies ∫_{z≤−1} generatorIntegrand w y z ν(dz) ≥−ν((−∞,−1])w(y). Uses authentic ν_integrable and Proved pointwise source jump-integrand lower bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_large_negative_jump_generator_integral_lower_floor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (y : ℝ)
    (hwpos : ∀ u : ℝ, 0 ≤ w u)
    (hderiv : 0 ≤ deriv w y)
    (hGen : X.GeneratorIntegrable w y) :
    -(X.ν (Iic (-1 : ℝ))).toReal * w y ≤
      ∫ z in Iic (-1 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν := by sorry
