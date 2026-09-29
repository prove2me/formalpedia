-- Prove2me | solution 1 for quadratic_neumann_first_index_distinct_centered_coefficient_as_off_diagonal_response
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-20T16:42:10.592947+00:00
-- url     : https://prove2.me/submissions/4f5f5f53-7855-4e39-8d5f-2d42d5d6a257

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped Classical BigOperators

theorem solution
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega2 : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    quadraticFirstIndexDistinctCenteredCoefficientMatrix Omega2 S p =
      offDiagonalTangentResponse S
        (centeredSamplingFluctuation Omega2 p
          (linearNeumannDiagonalBaseMatrix S)) := by
  ext i j
  unfold quadraticFirstIndexDistinctCenteredCoefficientMatrix offDiagonalTangentResponse
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hw : w = (i, j)
  · simp [hw]
  · rw [if_neg hw, if_neg hw]
    unfold centeredSamplingFluctuation centeredIndicator
    simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, samplingProjection,
      linearNeumannDiagonalBaseMatrix, tangentDiagonalMultiplier]
    by_cases hm : (w.1, w.2) ∈ Omega2
    · simp only [hm, if_true]; ring
    · simp only [hm, if_false]; ring
