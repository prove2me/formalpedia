-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_uniform_grid_linear_rate_sum_real
-- name    : AvramDividend.Classical.avram_p2_e_compensator_uniform_grid_linear_rate_sum_real
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:43:26.886615+00:00
-- url     : https://prove2.me/theorems/4b319c0b-ca62-48ef-a231-5f6795f1369d
-- title:
--   Real triangular sum of physical uniform-cell past-future factorial mean rates
-- statement:
--   The triangular sum of i times a squared real per-cell rate over i from zero to k is k(k+1)/2 times that squared rate. This is the deterministic algebraic part of the original negative-band grid second-factorial moment.
-- source:
--   Pinned Fin.sum_univ_castSucc and Finset.sum_mul, independent of stochastic assumptions, for original grid rectangular mean rate summation.

import Mathlib

open scoped BigOperators

theorem AvramDividend.Classical.avram_p2_e_compensator_uniform_grid_linear_rate_sum_real (k : ℕ) (a : ℝ) :
    (∑ i : Fin (k + 1), (i.val : ℝ) * a ^ 2) =
      (k : ℝ) * ((k : ℝ) + 1) / 2 * a ^ 2 := by sorry
