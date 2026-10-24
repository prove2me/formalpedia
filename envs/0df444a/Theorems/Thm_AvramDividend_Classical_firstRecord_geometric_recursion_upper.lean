-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstRecord_geometric_recursion_upper
-- name    : AvramDividend.Classical.firstRecord_geometric_recursion_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:01:28.037741+00:00
-- url     : https://prove2.me/theorems/a3284bf7-ec66-4f76-b3bb-084af581cb5a
-- title:
--   Iterate the one-step discounted first-record upper estimate
-- statement:
--   Once the first-passage strong Markov property yields a one-step upper recurrence v_(n+1) ≤ p v_n and v_0≤1, the discounted first-record expectations are bounded by p^n for every n. This provides the induction part of the currently missing stochastic record estimates.
-- source:
--   Induction on record index, order-preserving multiplication in extended nonnegative reals.

import Mathlib.Data.ENNReal.Real
open scoped NNReal ENNReal

theorem AvramDividend.Classical.firstRecord_geometric_recursion_upper (p : ℝ≥0∞) (v : ℕ → ℝ≥0∞)
    (hzero : v 0 ≤ 1) (hstep : ∀ n, v (n + 1) ≤ p * v n) :
    ∀ n, v n ≤ p ^ n := by sorry
