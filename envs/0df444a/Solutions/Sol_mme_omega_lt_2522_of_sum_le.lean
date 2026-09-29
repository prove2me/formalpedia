-- Prove2me | solution 1 for mme_omega_lt_2522_of_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-23T23:05:09.861306+00:00
-- url     : https://prove2.me/submissions/0e3f6a31-c574-4d25-8722-e3c4e07a3769

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_mme_omega_strassen

open MME Real

universe u

set_option maxRecDepth 10000
set_option exponentiation.threshold 2000

private theorem rpow_110_bound_2522 :
    (52 : ℝ) < (110 : ℝ) ^ ((1261 : ℝ) / 1500) := by
  have hnat : (52 : ℕ) ^ 1500 < 110 ^ 1261 := by
    decide
  have h_eq : (110 : ℝ) ^ ((1261 : ℝ) / 1500) =
      ((110 : ℝ) ^ (1261 : ℕ)) ^ ((1 : ℝ) / 1500) := by
    rw [← rpow_natCast (110 : ℝ) 1261,
        ← rpow_mul (by positivity : (0 : ℝ) ≤ 110),
        show ((1261 : ℕ) : ℝ) * ((1 : ℝ) / 1500) =
            (1261 : ℝ) / 1500 by push_cast; ring]
  rw [h_eq, show (52 : ℝ) =
      (((52 : ℝ) ^ (1500 : ℕ)) ^ ((1 : ℝ) / 1500)) from by
    rw [← rpow_natCast (52 : ℝ) 1500,
        ← rpow_mul (by positivity : (0 : ℝ) ≤ 52),
        show ((1500 : ℕ) : ℝ) * ((1 : ℝ) / 1500) = 1 by push_cast; ring,
        rpow_one]]
  exact rpow_lt_rpow (by positivity) (by exact_mod_cast hnat) (by positivity)

theorem solution {K : Type u} [Field K]
    (h : 3 * (110 : ℝ) ^ (matMulExp_strassen K / 3) ≤ 156) :
    matMulExp_strassen K < 1261 / 500 := by
  by_contra h_ge
  rw [not_lt] at h_ge
  have h_exp : (1261 : ℝ) / 1500 ≤ matMulExp_strassen K / 3 := by
    linarith
  have h110 :
      (110 : ℝ) ^ ((1261 : ℝ) / 1500) ≤
        (110 : ℝ) ^ (matMulExp_strassen K / 3) :=
    rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 110) h_exp
  linarith [rpow_110_bound_2522]
