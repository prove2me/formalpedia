-- Prove2me | solution 1 for linear_neumann_diagonal_mean_as_scaled_diagonal_multiplier
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-20T15:51:10.53052+00:00
-- url     : https://prove2.me/submissions/0440c76e-a710-488a-8214-bdc9b72c03ec

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped Classical BigOperators

theorem solution {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (p : ℝ) :
    linearNeumannDiagonalMeanContribution S p =
      (p⁻¹ * (1 - p)) • tangentDiagonalMultiplier S (signMatrix S) := by
  unfold linearNeumannDiagonalMeanContribution
  ext i j
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  rw [Finset.sum_eq_single (i, j)]
  · have h1 : coordinateMatrix (i, j).1 (i, j).2 i j = 1 := by simp [coordinateMatrix]
    rw [h1]
    simp only [tangentDiagonalMultiplier]
    by_cases hp : p = 0
    · simp [hp]
    · have hpp : p⁻¹ * p = 1 := inv_mul_cancel₀ hp
      linear_combination (p⁻¹ * (1 - p) * signMatrix S i j * tangentCoordinateKernel S i j i j) * hpp
  · intro w _ hw
    have hne : ¬ (i = w.1 ∧ j = w.2) := by
      rintro ⟨hi, hj⟩
      exact hw (Prod.ext hi.symm hj.symm)
    simp only [coordinateMatrix, if_neg hne, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h
