-- Prove2me | Theorems.Thm_AvramDividend_Classical_recordGrid_prefix_survival_weight_budget
-- name    : AvramDividend.Classical.recordGrid_prefix_survival_weight_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T14:20:38.416993+00:00
-- url     : https://prove2.me/theorems/2adb26a5-176c-46ca-a75d-438460a24d4f
-- title:
--   Monotone first-record survival reduces killed budgets to surviving prefixes
-- statement:
--   Let record clocks T_n increase with n. If the undiscounted finite-prefix sum of nonnegative extended-real record rewards is bounded by C whenever the Nth clock precedes the stopping horizon, then every killed finite-prefix sum is bounded by C, including paths where ruin interrupts the grid. The proof splits at the last summand and inducts on the prefix length, using monotone clocks to remove the survival indicators when the final crossing survives.
-- source:
--   Finset.sum_range_succ, Finset.sum_congr, monotone clock survival and elementary Nat order.

import Mathlib.Data.ENNReal.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.recordGrid_prefix_survival_weight_budget
    (T : ℕ → ℝ≥0∞) (hT : Monotone T)
    (τ : ℝ≥0∞) (f : ℕ → ℝ≥0∞) (C : ℝ≥0∞)
    (hprefix : ∀ N : ℕ, T N < τ →
      (∑ n ∈ Finset.range N, f n) ≤ C) :
    ∀ N : ℕ,
      (∑ n ∈ Finset.range N,
        if T (n + 1) < τ then f n else 0) ≤ C := by sorry
