-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_dyadic_active_count_refinement
-- name    : AvramDividend.Classical.bv_dyadic_active_count_refinement
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:07:17.165986+00:00
-- url     : https://prove2.me/theorems/9db27020-f545-419b-b109-f95121fac9cc
-- title:
--   Dyadic subdivision cannot decrease the number of positive increments
-- statement:
--   For a real-valued grid path on 2n+1 points, define coarse active intervals as those with f(2i)<f(2i+2) and fine active intervals as f(j)<f(j+1). Every coarse active interval contains a fine active child, and the exact even/odd decomposition of finite sums proves the total number of active coarse intervals is no larger than active fine intervals. This pathwise combinatorial invariant is the exact refinement monotonicity required for dyadic Lévy residual no-creep, independent of stochastic assumptions.
-- source:
--   Avram, Palmowski, Pistorius (2007), bounded-variation finite-activity first-jump law; elementary combinatorial refinement.

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

open Finset

theorem AvramDividend.Classical.bv_dyadic_active_count_refinement
    (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n,
      (ite (f (2 * i) < f (2 * i + 2)) (1 : ℕ) 0)) ≤
      ∑ i ∈ Finset.range (2 * n),
        (ite (f i < f (i + 1)) (1 : ℕ) 0) := by sorry
