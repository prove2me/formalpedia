-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_weighted_image_kmoment_finite
-- name    : AvramDividend.Classical.avram_p2_b_rate_original_weighted_image_kmoment_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:12:36.572207+00:00
-- url     : https://prove2.me/theorems/08267e91-9eb4-4caf-8071-96c6f86142c8
-- title:
--   Original process all polynomial moments of fourth-weight exponential image measure are finite
-- statement:
--   For the original spectrally negative Levy process, and each nonnegative theta, time and integer k, the kth ENNReal moment of the fourth exponentially weighted exponential-image push-forward measure is finite. Derived from the original process Laplace integrability and the generic weighted image finite moment theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_weighted_integer_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_integrable_weighted_image_kmoment_finite

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_b_rate_original_weighted_image_kmoment_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : ∀ t : ℝ≥0, Measurable (X.X t))
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) (k : ℕ) :
    (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
      ((P.withDensity (fun ω =>
        ENNReal.ofReal ((Real.exp (θ * X.X t ω) - 1) ^ 4))).map
        (fun ω => Real.exp (θ * X.X t ω)))) < ⊤  := by sorry
