-- Prove2me | solution 1 for linear_neumann_correction_lambda_bound_le_one_eighth
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-20T15:40:03.602523+00:00
-- url     : https://prove2.me/submissions/ddc5e369-a014-4532-843a-8f5143cd63fe

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped Classical BigOperators

theorem solution
    (C₁ : ℝ) (hC₁ : 0 < C₁) :
    C₁ * Real.rpow (max 1 (8 * C₁)) (-1) ≤ (1 : ℝ) / 8 := by
  set D := max (1:ℝ) (8 * C₁) with hD
  have hD1 : (1:ℝ) ≤ D := le_max_left _ _
  have hDpos : 0 < D := lt_of_lt_of_le one_pos hD1
  have hrpow : Real.rpow D (-1) = D⁻¹ := by
    rw [show Real.rpow D (-1) = D ^ (-1:ℝ) from rfl, Real.rpow_neg_one]
  rw [hrpow]
  have hd8 : 8 * C₁ ≤ D := le_max_right _ _
  have hinv : D⁻¹ ≤ (8 * C₁)⁻¹ := by gcongr
  calc C₁ * D⁻¹ ≤ C₁ * (8 * C₁)⁻¹ := mul_le_mul_of_nonneg_left hinv (le_of_lt hC₁)
    _ = 1/8 := by field_simp
