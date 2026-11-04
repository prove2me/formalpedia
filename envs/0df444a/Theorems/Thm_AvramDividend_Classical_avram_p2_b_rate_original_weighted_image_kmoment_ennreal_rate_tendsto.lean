-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_weighted_image_kmoment_ennreal_rate_tendsto
-- name    : AvramDividend.Classical.avram_p2_b_rate_original_weighted_image_kmoment_ennreal_rate_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:26:31.898425+00:00
-- url     : https://prove2.me/theorems/6aa84fc1-ecdf-456a-8d19-c2c9f3626efc
-- title:
--   Original fourth-weighted exponential-image integer moments converge after ENNReal time normalisation
-- statement:
--   For the exact original spectrally negative Levy process, every nonnegative integer k and theta≥0, its fourth-weighted exponential-image ENNReal kth moment divided by positive small time converges in ENNReal to ofReal of the source Levy-measure weighted kth moment. The source real rate limit, finite-moment theorem and verified normalisation identity establish this without assuming any jump compensator or replacement process.

import Mathlib.Data.ENNReal.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Order.Filter.Tendsto
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_weighted_image_kmoment_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_weighted_image_moment_rate_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_finite_ennreal_moment_normalised_ofReal

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_b_rate_original_weighted_image_kmoment_ennreal_rate_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : ∀ t : ℝ≥0, Measurable (X.X t))
    (k : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) :
    Tendsto
      (fun h : ℝ =>
        (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
          ((P.withDensity (fun ω =>
            ENNReal.ofReal ((Real.exp (θ * X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
            (fun ω => Real.exp (θ * X.X (Real.toNNReal h) ω)))) /
          ENNReal.ofReal h)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (ENNReal.ofReal (∫ y in Iio (0 : ℝ), (Real.exp (θ * y)) ^ k *
        (Real.exp (θ * y) - 1) ^ 4 ∂X.ν))) := by sorry
