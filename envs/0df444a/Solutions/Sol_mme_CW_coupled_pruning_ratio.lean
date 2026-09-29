-- Prove2me | solution 1 for mme_CW_coupled_pruning_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T04:31:15.663722+00:00
-- url     : https://prove2.me/submissions/1b6b0732-c9d1-4e9d-9fc4-565b2f81f576

import Definitions.Def_mme_CW_coupled_value

/-!
# The numerical ratio used in the coupled-piece pruning

On CW90 journal p. 272 the optimized block proportions satisfy
`G / L = q^(3*tau) / 2`.  The proof needs this ratio to exceed `3.41`.
The published hypotheses give the stronger lower bound `9/2`.
-/

open MME Real

theorem solution
    (q : ℕ) (hq : 3 ≤ q) (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    (341 : ℝ) / 100 < (q : ℝ) ^ (3 * tau) / 2 := by
  have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by linarith
  have hpow : (q : ℝ) ^ (2 : ℝ) ≤ (q : ℝ) ^ (3 * tau) :=
    Real.rpow_le_rpow_of_exponent_le hq1 htau
  have hpowNat : (q : ℝ) ^ (2 : ℕ) ≤ (q : ℝ) ^ (3 * tau) := by
    rw [← Real.rpow_natCast]; exact_mod_cast hpow
  calc
    (341 : ℝ) / 100 < 9 / 2 := by norm_num
    _ ≤ (q : ℝ) ^ (2 : ℕ) / 2 := by
      gcongr
      nlinarith [sq_nonneg ((q : ℝ) - 3)]
    _ ≤ (q : ℝ) ^ (3 * tau) / 2 := by gcongr
