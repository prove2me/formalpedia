-- Prove2me | solution 1 for quadratic_neumann_all_equal_mean_as_scaled_base_matrix
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-20T15:51:53.051026+00:00
-- url     : https://prove2.me/submissions/f6b418d0-99a3-4688-bc5d-60a2bef58c6a

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped Classical BigOperators

theorem solution
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (p : ℝ) :
    quadraticNeumannAllEqualMeanContribution S p =
      ((p⁻¹) ^ 2 * (1 - 3 * p + 2 * p ^ 2)) •
        quadraticNeumannAllEqualBaseMatrix S := by
  ext i j
  simp only [quadraticNeumannAllEqualMeanContribution, quadraticNeumannAllEqualBaseMatrix,
    tangentDiagonalMultiplier, linearNeumannDiagonalBaseMatrix,
    Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  rw [Finset.sum_eq_single (i, j)]
  · have h1 : coordinateMatrix (i, j).1 (i, j).2 i j = 1 := by simp [coordinateMatrix]
    rw [h1]; ring
  · intro w _ hw
    have hne : ¬ (i = w.1 ∧ j = w.2) := by
      rintro ⟨hi, hj⟩
      exact hw (Prod.ext hi.symm hj.symm)
    simp only [coordinateMatrix, if_neg hne, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h
