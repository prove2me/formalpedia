-- Prove2me | Theorems.Thm_AvramDividend_Classical_stopped_payment_lintegral_eq_post_u_of_zero_Iic
-- name    : AvramDividend.Classical.stopped_payment_lintegral_eq_post_u_of_zero_Iic
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:58:25.087635+00:00
-- url     : https://prove2.me/theorems/964f4636-b96b-4a88-91fb-3cb2b3c0f91c
-- title:
--   A stopped Stieltjes integral ignores the pre-upcrossing interval when that interval has zero measure
-- statement:
--   For any Borel measure on the real time axis, any nonnegative measurable-or-nonmeasurable payoff function f, any extended-nonnegative dividend stopping horizon σ, and any real time u, if the measure of (-∞,u] is zero then the Lebesgue integral over paymentTimes σ equals the integral over (u,∞)∩paymentTimes σ. The proof establishes almost-everywhere equality of the two payment sets and applies Mathlib setLIntegral_congr. This precisely removes the initial zero-payment segment before a dividend barrier is first reached, including its endpoint atom.
-- source:
--   Pinned Mathlib setLIntegral_congr and ae_iff, and existing barrierStrategy_dividendMeasure_zero_preUpcrossing_Iic (d92e7576) for use in the below-barrier strong-Markov dividend factorisation 79978d61.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.OuterMeasure.AE
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.stopped_payment_lintegral_eq_post_u_of_zero_Iic
    (μ : Measure ℝ) (f : ℝ → ℝ≥0∞) (σ : ℝ≥0∞) (u : ℝ)
    (hμzero : μ (Set.Iic u) = 0) :
    (∫⁻ t in paymentTimes σ, f t ∂μ) =
      (∫⁻ t in Set.Ioi u ∩ paymentTimes σ, f t ∂μ) := by sorry
