-- Prove2me | Theorems.Thm_AvramDividend_Classical_paymentTimes_lintegral_le_of_rational_prefix_bounds
-- name    : AvramDividend.Classical.paymentTimes_lintegral_le_of_rational_prefix_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:51:02.072993+00:00
-- url     : https://prove2.me/theorems/47c77755-31e3-4769-8f51-2b914690c8ef
-- title:
--   Uniform bounds on all strict rational payment prefixes control the full stopped integral
-- statement:
--   A nonnegative Lebesgue integral over the exact stopped payment-time set is bounded by a constant if all rational left-closed time prefixes strictly below the killing time obey that constant. Proof uses the established rational-prefix exhaustion and Mathlib's directed union of set integrals. This permits finite surviving-horizon dividend record bounds to control the complete pre-ruin payout.
-- source:
--   Use paymentTimes_eq_iUnion_strict_rational_prefixes and setLIntegral_iUnion_of_directed on the directed family of rational prefixes, then iSup_le.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_paymentTimes_eq_iUnion_strict_rational_prefixes

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.paymentTimes_lintegral_le_of_rational_prefix_bounds
    (μ : Measure ℝ) (f : ℝ → ℝ≥0∞) (τ C : ℝ≥0∞)
    (hτ : 0 < τ)
    (hprefix : ∀ q : {q : ℚ // 0 < (q : ℝ) ∧ ENNReal.ofReal (q : ℝ) < τ},
      (∫⁻ x in Ico (0 : ℝ) (q.val : ℝ), f x ∂μ) ≤ C) :
    (∫⁻ x in paymentTimes τ, f x ∂μ) ≤ C := by sorry
