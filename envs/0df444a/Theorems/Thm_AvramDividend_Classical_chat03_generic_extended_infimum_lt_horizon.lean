-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_generic_extended_infimum_lt_horizon
-- name    : AvramDividend.Classical.chat03_generic_extended_infimum_lt_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T06:30:31.749896+00:00
-- url     : https://prove2.me/theorems/6fe34389-7bc2-4c6f-82b6-78ebf9d4a7f0
-- title:
--   A generic ENNReal strict first-passage infimum is below a finite horizon iff some witness is earlier
-- statement:
--   For an arbitrary predicate p on nonnegative real times and a finite nonnegative horizon T, the extended-real infimum of times satisfying p is strictly below T if and only if an actual witness s<T satisfies p. This handles empty witness sets and first passage infima which are not attained at the infimum. The result is independent of all stochastic assumptions and applies to either named strict first-passage time.
-- source:
--   Pinned Mathlib iInf_lt_iff and ENNReal.coe_lt_coe, verified by private Prove2Me elaboration at revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Data.ENNReal.Basic

open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat03_generic_extended_infimum_lt_horizon
    (p : ℝ≥0 → Prop) (T : ℝ≥0) :
    ((⨅ (s : ℝ≥0) (_ : p s), (s : ℝ≥0∞)) < (T : ℝ≥0∞)) ↔
      ∃ s : ℝ≥0, p s ∧ s < T := by sorry
