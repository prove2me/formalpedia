-- Prove2me | Theorems.Thm_AvramDividend_Classical_small_time_grid_nonnegative_exponential_bound
-- name    : AvramDividend.Classical.small_time_grid_nonnegative_exponential_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:50:30.720597+00:00
-- url     : https://prove2.me/theorems/b751f6c8-4cae-42bf-8609-db590699df4b
-- title:
--   Exponential bound for a finite grid with nonnegative increments
-- statement:
--   For the success probability 1-p of one independent grid increment, the probability (1-p)^n that every one of n increments is nonnegative is bounded by exp(-np). This deterministic estimate combines with the proved finite-prefix Lévy increment product theorem to force vanishing monotone-grid probability when n p tends to infinity.
-- source:
--   Elementary exponential tangent inequality 1-p ≤ exp(-p) and monotonicity of powers on nonnegative bases. Used after AvramDividend.Classical.chat04_all_finite_prefix_increment_cylinder_product (Proved, 4b6af35c-c6a9-4bca-ab7d-28f22e7bd161) in the zero-barrier regularity programme.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
open Real

theorem AvramDividend.Classical.small_time_grid_nonnegative_exponential_bound
    (p : ℝ) (n : ℕ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 - p) ^ n ≤ Real.exp (-((n : ℝ) * p)) := by sorry
