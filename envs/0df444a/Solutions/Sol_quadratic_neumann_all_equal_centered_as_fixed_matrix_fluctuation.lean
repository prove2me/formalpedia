-- Prove2me | solution 1 for quadratic_neumann_all_equal_centered_as_fixed_matrix_fluctuation
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-20T16:37:23.588786+00:00
-- url     : https://prove2.me/submissions/2f86932b-0551-4edc-a6ee-4c53d73478f1

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped Classical BigOperators

theorem solution
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    quadraticNeumannAllEqualCenteredContribution Omega S p =
      ((p⁻¹) ^ 2 * (1 - 3 * p + 3 * p ^ 2)) •
        centeredSamplingFluctuation Omega p
          (quadraticNeumannAllEqualBaseMatrix S) := by
  ext i j
  unfold quadraticNeumannAllEqualCenteredContribution
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  rw [Finset.sum_eq_single (i, j)]
  · have h1 : coordinateMatrix (i, j).1 (i, j).2 i j = 1 := by simp [coordinateMatrix]
    rw [h1]
    simp only [centeredIndicator, centeredSamplingFluctuation, samplingProjection,
      quadraticNeumannAllEqualBaseMatrix, linearNeumannDiagonalBaseMatrix,
      tangentDiagonalMultiplier, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    by_cases hm : (i, j) ∈ Omega
    · simp only [hm, if_true]; ring
    · simp only [hm, if_false]; ring
  · intro w _ hw
    have hne : ¬ (i = w.1 ∧ j = w.2) := fun ⟨hi, hj⟩ => hw (Prod.ext hi.symm hj.symm)
    simp only [coordinateMatrix, if_neg hne, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h
