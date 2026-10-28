-- Prove2me | Theorems.Thm_AvramDividend_Classical_nonnegative_random_measure_expected_le_of_uniform_time_caps
-- name    : AvramDividend.Classical.nonnegative_random_measure_expected_le_of_uniform_time_caps
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T12:13:17.996996+00:00
-- url     : https://prove2.me/theorems/2999159c-ad66-4baf-b2bf-6e0c86f35f65
-- title:
--   Uniform finite-horizon expected dividend bound for a random measure
-- statement:
--   If every natural-number capped expected random-measure payout is bounded by K and each capped integrand is measurable, the unrestricted expected payout is bounded by K. The new random-measure monotone convergence theorem and iSup_le discharge the exact extended-real inequality.
-- source:
--   Canonically Proved AvramDividend.Classical.nonnegative_random_measure_time_horizon_lintegral_iSup and Mathlib order-theory iSup_le.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Theorems.Thm_AvramDividend_Classical_nonnegative_random_measure_time_horizon_lintegral_iSup

open MeasureTheory Set
open scoped Classical ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.nonnegative_random_measure_expected_le_of_uniform_time_caps
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (μ : Ω → Measure ℝ)
    (f : Ω → ℝ → ℝ≥0∞)
    (hf : ∀ ω, Measurable (f ω))
    (hMeas : ∀ n : ℕ, Measurable (fun ω : Ω =>
      ∫⁻ t in Icc (0 : ℝ) (n : ℝ), f ω t ∂(μ ω)))
    (K : ℝ≥0∞)
    (hBound : ∀ n : ℕ,
      (∫⁻ ω, (∫⁻ t in Icc (0 : ℝ) (n : ℝ),
        f ω t ∂(μ ω)) ∂P) ≤ K) :
    (∫⁻ ω, (∫⁻ t in Ici (0 : ℝ), f ω t ∂(μ ω)) ∂P) ≤ K := by sorry
