-- Prove2me | solution 1 for mme_CW_numeric_optimum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-05-31T18:10:53.220872+00:00
-- url     : https://prove2.me/submissions/d0b4d260-2b35-458b-8b7e-74d2bc473ec6

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.NormNum

theorem solution : Real.log 8 / Real.log (5 / 2) < 2376 / 1000 := by
  have h_log_2_lt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have h_log_2_gt : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have h_log_8 : Real.log 8 = 3 * Real.log 2 := by
    have h82 : (8 : ℝ) = 2^3 := by norm_num
    rw [h82, Real.log_pow]; push_cast; ring
  have h_log_52_pos : 0 < Real.log (5/2) := Real.log_pos (by norm_num)
  have h_log_54 : (2:ℝ)/9 < Real.log (5/4) := by
    have h1 : (5/4 : ℝ) = 1 + 1/4 := by norm_num
    rw [h1]
    have h2 : (2:ℝ)/9 = 2 * (1/4) / ((1/4) + 2) := by ring
    rw [h2]
    exact Real.lt_log_one_add_of_pos (by norm_num : (0:ℝ) < 1/4)
  have h_log_52_eq : Real.log (5/2) = Real.log 2 + Real.log (5/4) := by
    have h52 : (5/2 : ℝ) = 2 * (5/4) := by norm_num
    rw [h52, Real.log_mul (by norm_num) (by norm_num)]
  have h_log_52_gt : Real.log (5/2) > 0.6931471803 + 2/9 := by
    rw [h_log_52_eq]; linarith
  have h_log_8_lt : Real.log 8 < 3 * (0.6931471808 : ℝ) := by
    rw [h_log_8]; linarith
  have h_num : 3 * (0.6931471808 : ℝ) ≤ (2376/1000) * ((0.6931471803 : ℝ) + 2/9) := by
    norm_num
  have h_mul_gt : (2376/1000 : ℝ) * ((0.6931471803 : ℝ) + 2/9) < (2376/1000 : ℝ) * Real.log (5/2) :=
    mul_lt_mul_of_pos_left h_log_52_gt (by norm_num)
  have h_combine : Real.log 8 < (2376/1000 : ℝ) * Real.log (5/2) := by linarith
  rw [div_lt_iff₀ h_log_52_pos]
  linarith
