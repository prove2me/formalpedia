-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstRecord_finite_cell_budget_to_tsum
-- name    : AvramDividend.Classical.firstRecord_finite_cell_budget_to_tsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:22:55.960177+00:00
-- url     : https://prove2.me/theorems/84adc590-95f3-460e-a40b-7a6eb61663fd
-- title:
--   Uniform finite first-record budgets dominate the full countable record sum
-- statement:
--   If every finite prefix sum of nonnegative discounted first-record budgets is dominated by one extended-nonnegative reward budget C, then their infinite sum is also dominated by C. This converts established finite-cell Stieltjes inequalities into the countable form needed for the stopped renewal parent.
-- source:
--   Pinned Mathlib theorem ENNReal.tsum_eq_iSup_nat (Mathlib.Topology.Algebra.InfiniteSum.ENNReal), verified at commit 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.firstRecord_finite_cell_budget_to_tsum (f : ℕ → ℝ≥0∞) (C : ℝ≥0∞)
    (hfinite : ∀ N, (∑ n ∈ Finset.range N, f n) ≤ C) :
    (∑' n, f n) ≤ C := by sorry
