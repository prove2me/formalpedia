-- Prove2me | Theorems.Thm_AvramDividend_Classical_exp_neg_remainder_bounds
-- name    : AvramDividend.Classical.exp_neg_remainder_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T15:43:04.841985+00:00
-- url     : https://prove2.me/theorems/1f93d37b-ef44-4ffd-9b86-55460e78a973
-- title:
--   Quadratic bound for the compensated exponential on the negative half-line
-- statement:
--   For every nonpositive real z, the compensated exponential remainder exp(z)-1-z is between zero and z squared. This is the pointwise analytic estimate needed to dominate the small negative jumps in the canonical Lévy-Khintchine exponent.
-- source:
--   Real.add_one_le_exp, Real.abs_exp_sub_one_sub_id_le, and Real.exp_le_one_iff in pinned Mathlib. The Lévy-exponent bound psi_quadratic_upper applies this with z=theta*y for y in (-1,0).

import Mathlib

theorem AvramDividend.Classical.exp_neg_remainder_bounds (z : ℝ) (hz : z ≤ 0) :
    0 ≤ Real.exp z - 1 - z ∧ Real.exp z - 1 - z ≤ z ^ 2 := by sorry
