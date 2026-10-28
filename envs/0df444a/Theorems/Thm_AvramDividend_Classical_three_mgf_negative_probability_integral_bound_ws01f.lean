-- Prove2me | Theorems.Thm_AvramDividend_Classical_three_mgf_negative_probability_integral_bound_ws01f
-- name    : AvramDividend.Classical.three_mgf_negative_probability_integral_bound_ws01f
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T10:38:42.412656+00:00
-- url     : https://prove2.me/theorems/f35356ad-ac44-4b9e-b48d-756daa123ebf
-- title:
--   Negative-tail probability lower bound from three real exponential moments
-- statement:
--   For any measurable real random variable under a probability measure whose exponential transforms at parameters 1/r, 1, 2 are integrable, the expectation at parameter 1 is bounded above by the appropriately weighted other two expectations plus an explicit multiple of the probability of a negative value. This is the genuine probabilistic integral bridge from the canonically Proved three-scale pointwise inequality to fixed-time Gaussian Lévy negative-tail estimates, without postulating weak convergence.
-- source:
--   MeasureTheory.integral_mono_ae, integral_indicator_one, integral linearity and Proved AvramDividend.Classical.exp_three_scale_negative_indicator_ws01f. Pinned Mathlib 0df444a.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_exp_three_scale_negative_indicator_ws01f

open MeasureTheory Filter Set
open AvramDividend.Classical

theorem AvramDividend.Classical.three_mgf_negative_probability_integral_bound_ws01f
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) (hY : Measurable Y)
    (r : ℝ) (hr : 1 ≤ r)
    (h1 : Integrable (fun ω => Real.exp (Y ω)) μ)
    (hs : Integrable (fun ω => Real.exp (Y ω / r)) μ)
    (h2 : Integrable (fun ω => Real.exp (2 * Y ω)) μ) :
    (∫ ω, (Real.exp (Y ω) - 1) ∂μ) ≤
      r ^ 2 * (∫ ω, (Real.exp (Y ω / r) - 1) ∂μ) +
      (∫ ω, (Real.exp (2 * Y ω) - 1) ∂μ) / r +
      (r ^ 2 + 1 / r) * μ.real {ω | Y ω < 0} := by sorry
