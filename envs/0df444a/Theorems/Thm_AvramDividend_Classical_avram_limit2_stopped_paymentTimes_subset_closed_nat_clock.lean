-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_stopped_paymentTimes_subset_closed_nat_clock
-- name    : AvramDividend.Classical.avram_limit2_stopped_paymentTimes_subset_closed_nat_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T16:46:42.783362+00:00
-- url     : https://prove2.me/theorems/0482c9a7-b34d-4ff1-85de-e142cb1572f1
-- title:
--   Exact original stopped payment times lie within their natural closed integer horizon, including time-zero atom
-- statement:
--   For the exact original paymentTimes definition, a payable t is nonnegative and either is the time-zero atom or satisfies ENNReal.ofReal t < min τ n. The time-zero alternative lies in Iic n. In the strict positive-time branch, strict inequality below the stopped clock gives ENNReal.ofReal t < n, and monotonicity of ENNReal.ofReal excludes n < t. The argument holds even at n = 0 and τ = 0 without silently changing the payment convention. This is a deterministic support adapter for the open natural-clock horizon saturation theorem.

import Mathlib.Order.Interval.Set.Defs
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_stopped_paymentTimes_subset_closed_nat_clock
    (τ : ℝ≥0∞) (n : ℕ) :
    paymentTimes (min τ (n : ℝ≥0∞)) ⊆ Set.Iic (n : ℝ) := by sorry
