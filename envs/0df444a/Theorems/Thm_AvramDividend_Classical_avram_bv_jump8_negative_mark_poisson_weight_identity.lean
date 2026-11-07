-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_negative_mark_poisson_weight_identity
-- name    : AvramDividend.Classical.avram_bv_jump8_negative_mark_poisson_weight_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T13:43:14.682191+00:00
-- url     : https://prove2.me/theorems/7f90fc12-e3d1-4d07-b2f0-fdbe69997ec2
-- title:
--   Exact intrinsic negative-mark exponential equals Poisson count power weight
-- statement:
--   For a strictly negative source jump mark y, the literal ENNReal.ofReal(-y) weight raised through n marked counts has the exact real exponential factor exp(y)^n. This is the algebraic bridge needed to apply a Poisson probability-generating transform with coefficient exp(y), respecting y<0 rather than replacing actual jump marks by abstract counts.
-- source:
--   For y<0, -y≥0 and ENNReal.toReal_ofReal gives the exact nonnegative real jump magnitude. Algebra reduces minus n times minus y to n*y, and Real.exp_nat_mul gives the Poisson count power.

import Mathlib
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_negative_mark_poisson_weight_identity
    (y : ℝ) (hy : y < 0) (n : ℕ) :
    Real.exp (-((n : ℝ) * (ENNReal.ofReal (-y)).toReal)) =
      (Real.exp y) ^ n := by sorry
