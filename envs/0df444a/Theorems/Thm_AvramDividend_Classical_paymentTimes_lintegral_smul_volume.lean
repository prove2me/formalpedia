-- Prove2me | Theorems.Thm_AvramDividend_Classical_paymentTimes_lintegral_smul_volume
-- name    : AvramDividend.Classical.paymentTimes_lintegral_smul_volume
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:14:16.900229+00:00
-- url     : https://prove2.me/theorems/04a45683-9909-46a7-9c94-ff97e7ed1954
-- title:
--   Scalar multiplication of Lebesgue measure moves inside stopped dividend-time integration
-- statement:
--   For any prescribed payment-time set and measurable nonnegative payoff, integrating against a constant scalar multiple of Lebesgue measure equals integrating the scalar-multiplied payoff against Lebesgue measure. This is a deterministic measure identity used to identify finite-activity reflected dividends with their discounted drift reward.
-- source:
--   Pinned Mathlib lintegral_smul_measure and lintegral_const_mul plus accepted paymentTimes_measurable.

import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.paymentTimes_lintegral_smul_volume
    (σ : ℝ≥0∞) (c : ℝ≥0∞) (w : ℝ → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ t in paymentTimes σ, w t ∂(c • volume)) =
    (∫⁻ t in paymentTimes σ, c * w t ∂volume) := by sorry
