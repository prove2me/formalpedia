-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_weighted_exponential_image_moment_integral_eq
-- name    : AvramDividend.Classical.avram_p2_b_rate_weighted_exponential_image_moment_integral_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:06:11.844883+00:00
-- url     : https://prove2.me/theorems/c9830abb-3167-40f7-b8c8-cb7298443acd
-- title:
--   Finite weighted exponential-image kth moments equal ENNReal lifts of original Bochner moments
-- statement:
--   Under the precise original integrability of exp(theta Y)^k times the nonnegative fourth-exponential weight, the nonnegative kth lower integral of the weighted image measure equals ENNReal.ofReal of the source-weighted real Bochner integral. This exact identification bridges small-time real Laplace derivatives to finite weighted-image measure moments without assuming jump intensity.

import Mathlib
import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_weighted_exponential_image_lintegral

open MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_b_rate_weighted_exponential_image_moment_integral_eq
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : Ω → ℝ) (hY : Measurable Y) (θ : ℝ) (k : ℕ)
    (hInt : Integrable (fun ω =>
      (Real.exp (θ * Y ω)) ^ k *
        (Real.exp (θ * Y ω) - 1) ^ 4) μ) :
    (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
      ((μ.withDensity (fun ω =>
        ENNReal.ofReal ((Real.exp (θ * Y ω) - 1) ^ 4))).map
        (fun ω => Real.exp (θ * Y ω)))) =
    ENNReal.ofReal (∫ ω,
      (Real.exp (θ * Y ω)) ^ k *
        (Real.exp (θ * Y ω) - 1) ^ 4 ∂μ)  := by sorry
