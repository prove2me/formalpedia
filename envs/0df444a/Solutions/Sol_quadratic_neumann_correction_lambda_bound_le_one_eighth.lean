-- Prove2me | solution 1 for quadratic_neumann_correction_lambda_bound_le_one_eighth
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T03:08:33.815511+00:00
-- url     : https://prove2.me/submissions/2921ac08-cd49-4f10-a14c-8f22dc4dff16

import Definitions.Def_matrix_completion_neumann
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

open MatrixCompletion

theorem solution
    (C₂ : ℝ) (hC₂ : 0 < C₂) :
    C₂ * Real.rpow (max 1 ((8 * C₂) ^ 2)) (-((3 : ℝ) / 2)) ≤
      (1 : ℝ) / 8 := by
  by_cases hsmall : 8 * C₂ ≤ 1
  · have hsquare_le : (8 * C₂) ^ 2 ≤ (1 : ℝ) := by nlinarith
    rw [max_eq_left hsquare_le]
    have hC₂_le : C₂ ≤ (1 : ℝ) / 8 := by linarith
    simpa [Real.rpow_eq_pow] using hC₂_le
  · have hlarge : 1 ≤ 8 * C₂ := le_of_not_ge hsmall
    have hsquare_ge : (1 : ℝ) ≤ (8 * C₂) ^ 2 := by nlinarith
    rw [max_eq_right hsquare_ge, Real.rpow_eq_pow]
    rw [Real.rpow_neg (sq_nonneg (8 * C₂)) ((3 : ℝ) / 2)]
    rw [Real.rpow_div_two_eq_sqrt (3 : ℝ) (sq_nonneg (8 * C₂))]
    rw [Real.sqrt_sq_eq_abs]
    rw [abs_of_nonneg (by linarith : 0 ≤ 8 * C₂)]
    have hx_nonneg : 0 ≤ C₂ * 8 := by linarith
    have hx_sq_ge : 1 ≤ (C₂ * 8) ^ 2 := by
      nlinarith [sq_nonneg (C₂ * 8 - 1)]
    have hx_le_cube : C₂ * 8 ≤ (C₂ * 8) ^ 3 := by
      calc
        C₂ * 8 = (C₂ * 8) * 1 := by ring
        _ ≤ (C₂ * 8) * ((C₂ * 8) ^ 2) :=
          mul_le_mul_of_nonneg_left hx_sq_ge hx_nonneg
        _ = (C₂ * 8) ^ 3 := by ring
    field_simp [hC₂.ne']
    simpa [Real.rpow_natCast] using hx_le_cube
