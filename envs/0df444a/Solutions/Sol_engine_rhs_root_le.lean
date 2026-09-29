-- Prove2me | solution 1 for engine_rhs_root_le
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-06-25T02:41:39.649206+00:00
-- url     : https://prove2.me/submissions/4b6beefe-f67c-4a41-b805-abdad6aa4171

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import Theorems.Thm_double_factorial_central_quotient_le_two_p_pow
import Theorems.Thm_rank_rpow_inv_le_exp_one_of_log_le

open scoped BigOperators

theorem solution
    (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) (normV : ℝ) (hV : 0 ≤ normV)
    (hlog : Real.log (d : ℝ) ≤ (2 * n : ℕ)) :
    Real.rpow
      (((Nat.factorial (2 * n) : ℝ) / ((2 ^ n : ℝ) * (Nat.factorial n : ℝ)))
        * normV ^ n * (d : ℝ)) ((1 : ℝ) / (2 * n))
      ≤ Real.sqrt (2 * n : ℕ) * Real.exp 1 * Real.sqrt normV := by
  have h2n : (0:ℝ) < 2 * n := by positivity
  set dblfact : ℝ := (Nat.factorial (2 * n) : ℝ) / ((2 ^ n : ℝ) * (Nat.factorial n : ℝ)) with hdf
  have hdf0 : 0 ≤ dblfact := by rw [hdf]; positivity
  have hnV : (0:ℝ) ≤ normV ^ n := by positivity
  have hdR : (0:ℝ) ≤ (d : ℝ) := by positivity
  show (dblfact * normV ^ n * (d:ℝ)) ^ ((1:ℝ) / (2 * n))
      ≤ Real.sqrt (2 * n : ℕ) * Real.exp 1 * Real.sqrt normV
  rw [Real.mul_rpow (by positivity) hdR, Real.mul_rpow hdf0 hnV]
  have hf1 : dblfact ^ ((1:ℝ) / (2 * n)) ≤ Real.sqrt (2 * n : ℕ) := by
    have hpa : dblfact ≤ (2 * n : ℝ) ^ n := double_factorial_central_quotient_le_two_p_pow n
    calc dblfact ^ ((1:ℝ) / (2 * n))
        ≤ ((2 * n : ℝ) ^ n) ^ ((1:ℝ) / (2 * n)) := by
          apply Real.rpow_le_rpow hdf0 hpa (by positivity)
      _ = Real.sqrt (2 * n : ℕ) := by
          rw [← Real.rpow_natCast (2 * n : ℝ) n, ← Real.rpow_mul (by positivity),
              Real.sqrt_eq_rpow]
          congr 1
          · push_cast; ring
          · push_cast; field_simp
  have hf2 : (normV ^ n) ^ ((1:ℝ) / (2 * n)) = Real.sqrt normV := by
    rw [← Real.rpow_natCast normV n, ← Real.rpow_mul hV, Real.sqrt_eq_rpow]
    congr 1
    push_cast; field_simp
  have hf3 : (d : ℝ) ^ ((1:ℝ) / (2 * n)) ≤ Real.exp 1 := by
    have hw := rank_rpow_inv_le_exp_one_of_log_le d (2 * n : ℕ) hd (by
      have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
      push_cast; nlinarith) (by push_cast at hlog ⊢; linarith)
    rw [show ((2 * n : ℕ) : ℝ)⁻¹ = (1:ℝ) / (2 * n) by push_cast; rw [one_div]] at hw
    exact hw
  rw [hf2]
  have hsqV : (0:ℝ) ≤ Real.sqrt normV := Real.sqrt_nonneg _
  have hsq2n : (0:ℝ) ≤ Real.sqrt (2 * n : ℕ) := Real.sqrt_nonneg _
  have hposD : (0:ℝ) ≤ (d:ℝ) ^ ((1:ℝ)/(2*n)) := Real.rpow_nonneg hdR _
  calc dblfact ^ ((1:ℝ)/(2*n)) * Real.sqrt normV * (d:ℝ) ^ ((1:ℝ)/(2*n))
      ≤ Real.sqrt (2 * n : ℕ) * Real.sqrt normV * Real.exp 1 := by
        apply mul_le_mul _ hf3 hposD (by positivity)
        exact mul_le_mul hf1 (le_refl _) hsqV hsq2n
    _ = Real.sqrt (2 * n : ℕ) * Real.exp 1 * Real.sqrt normV := by ring
