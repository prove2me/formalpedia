-- Prove2me | solution 1 for mme_behrend_log_loss_absorbed_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T11:33:00.476603+00:00
-- url     : https://prove2.me/submissions/97fb7f1d-a4e0-4eb2-bdaf-b90a53fffa8f

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt

theorem solution
    (N H : ℕ) (hHbound : H ≤ 4 ^ N) :
    Real.exp (-200 * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
      Real.exp (-100 *
        Real.sqrt (Real.log (((H + 1 : ℕ) : ℝ)))) := by
  have hNr : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hNp1 : 0 ≤ (N : ℝ) + 1 := by positivity
  have hHcast : ((H + 1 : ℕ) : ℝ) ≤
      2 * ((4 : ℝ) ^ N) := by
    have hone_le : (1 : ℕ) ≤ 4 ^ N := by
      have hpow : 0 < 4 ^ N := pow_pos (by omega) N
      omega
    have hnat : H + 1 ≤ 2 * 4 ^ N := by omega
    exact_mod_cast hnat
  have hlogUpper :
      Real.log (((H + 1 : ℕ) : ℝ)) ≤
        4 * ((N : ℝ) + 1) := by
    have hlogMono :=
      Real.log_le_log (by positivity : (0 : ℝ) < ((H + 1 : ℕ) : ℝ))
        hHcast
    have hlogTwo : Real.log (2 : ℝ) ≤ 1 := by
      nlinarith [Real.log_le_sub_one_of_pos (by norm_num :
        (0 : ℝ) < 2)]
    have hlogFour : Real.log (4 : ℝ) ≤ 3 := by
      nlinarith [Real.log_le_sub_one_of_pos (by norm_num :
        (0 : ℝ) < 4)]
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (pow_ne_zero N (by norm_num : (4 : ℝ) ≠ 0)),
      Real.log_pow] at hlogMono
    push_cast at hlogMono
    have hNlog :
        (N : ℝ) * Real.log 4 ≤ (N : ℝ) * 3 :=
      mul_le_mul_of_nonneg_left hlogFour hNr
    rw [Nat.cast_add, Nat.cast_one]
    nlinarith
  have hsqrtLog :
      Real.sqrt (Real.log (((H + 1 : ℕ) : ℝ))) ≤
        2 * Real.sqrt ((N : ℝ) + 1) := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt hNp1]
  apply Real.exp_le_exp.mpr
  rw [Nat.cast_add, Nat.cast_one]
  nlinarith
