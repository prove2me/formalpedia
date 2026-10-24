-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstRecord_geometric_recursion_lower
-- name    : AvramDividend.Classical.firstRecord_geometric_recursion_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:01:28.217747+00:00
-- url     : https://prove2.me/theorems/00dbece0-b3d4-40c6-b83f-6705310b1b41
-- title:
--   Iterate the one-step discounted first-record lower estimate
-- statement:
--   Once the first-passage strong Markov property yields a one-step lower recurrence p v_n ≤ v_(n+1) and v_0≥1, discounted first-record expectations dominate p^n for every n. This provides the induction part of the currently missing stochastic record estimates.
-- source:
--   Induction on record index, order-preserving multiplication in extended nonnegative reals.

import Mathlib.Data.ENNReal.Real
open scoped NNReal ENNReal

theorem AvramDividend.Classical.firstRecord_geometric_recursion_lower (p : ℝ≥0∞) (v : ℕ → ℝ≥0∞)
    (hzero : 1 ≤ v 0) (hstep : ∀ n, p * v n ≤ v (n + 1)) :
    ∀ n, p ^ n ≤ v n := by sorry
