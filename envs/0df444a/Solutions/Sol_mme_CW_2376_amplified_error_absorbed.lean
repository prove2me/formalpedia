-- Prove2me | solution 1 for mme_CW_2376_amplified_error_absorbed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T05:42:00.451703+00:00
-- url     : https://prove2.me/submissions/3ded9b13-98d5-4701-8843-6d03c16be38f

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open Real

/-!
Convert the fixed 616627-fold coupled relative-error loss into a per-root loss
at the exact profile length 3000000*m.
-/

theorem solution
    (B rate delta : ℝ) (m : ℕ)
    (hB : 0 ≤ B)
    (hdelta_nonneg : 0 ≤ delta) (hdelta_lt : delta < 1)
    (hm : 1 ≤ m) :
    (B * Real.exp (-(rate + delta / (1 - delta)))) ^
        (3000000 * m) ≤
      (B * Real.exp (-rate)) ^ (3000000 * m) *
        (1 - delta) ^ (616627 : ℕ) := by
  have hone_sub_pos : 0 < 1 - delta := sub_pos.mpr hdelta_lt
  have hone_sub_nonneg : 0 ≤ 1 - delta := hone_sub_pos.le
  have hone_sub_le_one : 1 - delta ≤ 1 := by linarith
  have hlog :
      -delta / (1 - delta) ≤ Real.log (1 - delta) := by
    have h := Real.one_sub_inv_le_log_of_pos hone_sub_pos
    have hne : 1 - delta ≠ 0 := ne_of_gt hone_sub_pos
    convert h using 1 <;> field_simp <;> ring
  have hexp_le :
      Real.exp (-delta / (1 - delta)) ≤ 1 - delta := by
    calc
      Real.exp (-delta / (1 - delta))
          ≤ Real.exp (Real.log (1 - delta)) := Real.exp_le_exp.mpr hlog
      _ = 1 - delta := Real.exp_log hone_sub_pos
  have hcount : 616627 ≤ 3000000 * m := by omega
  have hloss_pow :
      Real.exp (-delta / (1 - delta)) ^ (3000000 * m) ≤
        (1 - delta) ^ (616627 : ℕ) := by
    calc
      Real.exp (-delta / (1 - delta)) ^ (3000000 * m)
          ≤ (1 - delta) ^ (3000000 * m) :=
        pow_le_pow_left₀ (by positivity) hexp_le _
      _ ≤ (1 - delta) ^ (616627 : ℕ) :=
        pow_le_pow_of_le_one hone_sub_nonneg hone_sub_le_one hcount
  have hbase :
      B * Real.exp (-(rate + delta / (1 - delta))) =
        (B * Real.exp (-rate)) *
          Real.exp (-delta / (1 - delta)) := by
    rw [show -(rate + delta / (1 - delta)) =
        -rate + (-delta / (1 - delta)) by ring, Real.exp_add]
    ring
  rw [hbase, mul_pow]
  exact mul_le_mul_of_nonneg_left hloss_pow
    (pow_nonneg (mul_nonneg hB (Real.exp_pos _).le) _)
