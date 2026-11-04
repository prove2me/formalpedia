-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_weighted_image_moment_rate_tendsto
-- name    : AvramDividend.Classical.avram_p2_b_rate_original_weighted_image_moment_rate_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:19:03.217599+00:00
-- url     : https://prove2.me/theorems/3a7b9ad9-688f-470b-aefd-97fc7958f74c
-- title:
--   Original Levy weighted exponential-image lower moment rates converge to original Levy measure moments
-- statement:
--   For each natural moment k, measurable original-process marginals and nonnegative theta, the small-time scaled toReal of the kth lower moment of its fourth-weighted exponential-image measure converges to the corresponding genuine X.nu weighted kth moment. This composes the original source finite-exponential derivative with a source-verified image-integral conversion, with no jump-rate hypothesis.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_fourth_weighted_integer_moments
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_weighted_integer_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_weighted_exponential_image_moment_integral_eq

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_b_rate_original_weighted_image_moment_rate_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : ∀ t : ℝ≥0, Measurable (X.X t))
    (k : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) :
    Tendsto
      (fun h : ℝ =>
        ((∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
          ((P.withDensity (fun ω =>
            ENNReal.ofReal ((Real.exp (θ * X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
            (fun ω => Real.exp (θ * X.X (Real.toNNReal h) ω)))).toReal / h))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∫ y in Iio (0 : ℝ), (Real.exp (θ * y)) ^ k *
        (Real.exp (θ * y) - 1) ^ 4 ∂X.ν))  := by sorry
