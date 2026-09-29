-- Prove2me | solution 1 for quadratic_neumann_last_index_distinct_mean_as_off_diagonal_response
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-20T16:45:29.008352+00:00
-- url     : https://prove2.me/submissions/e1b35414-7632-4598-91f1-3d26d2c891f1

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped Classical BigOperators

theorem solution
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    quadraticNeumannLastIndexDistinctMeanContribution Omega S p =
      (1 - p) •
        quadraticLastIndexDistinctOffDiagonalResponse S
          (centeredSamplingFluctuation Omega p (p⁻¹ • signMatrix S)) := by
  ext i j
  unfold quadraticNeumannLastIndexDistinctMeanContribution
    quadraticLastIndexDistinctOffDiagonalResponse
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w1 _
  apply Finset.sum_congr rfl
  intro w3 _
  by_cases hw : w1 = w3
  · simp [hw]
  · rw [if_neg hw, if_neg hw]
    unfold centeredSamplingFluctuation centeredIndicator
    simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, samplingProjection]
    by_cases hm : (w3.1, w3.2) ∈ Omega
    · simp only [hm, if_true]
      by_cases hp : p = 0
      · simp [hp]
      · field_simp
    · simp only [hm, if_false]
      by_cases hp : p = 0
      · simp [hp]
      · field_simp; ring
