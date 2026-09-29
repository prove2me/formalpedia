-- Prove2me | solution 1 for quadratic_neumann_middle_index_distinct_centered_coefficient_entry_as_signed_scalar_fluctuation
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-20T18:32:41.070903+00:00
-- url     : https://prove2.me/submissions/f35eaf73-7f35-4438-9a4a-296dfd1c793d

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped Classical BigOperators

private theorem csf_apply {n₁ n₂ : Nat} (Omega : Finset (Fin n₁ × Fin n₂)) (p : ℝ)
    (X : Matrix (Fin n₁) (Fin n₂) ℝ) (i : Fin n₁) (j : Fin n₂) :
    centeredSamplingFluctuation Omega p X i j
      = p⁻¹ * (centeredIndicator Omega p i j * X i j) := by
  unfold centeredSamplingFluctuation centeredIndicator
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, samplingProjection]
  by_cases hm : (i, j) ∈ Omega
  · simp only [hm, if_true]; ring
  · simp only [hm, if_false]; ring

theorem solution
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega2 : Finset (Fin n₁ × Fin n₂)) (S : SVD M r)
    (p : ℝ) (w1 : Fin n₁ × Fin n₂) :
    quadraticMiddleIndexDistinctCenteredCoefficientMatrix Omega2 S p
        w1.1 w1.2 =
      signMatrix S w1.1 w1.2 *
        matrixEntrySum
          (centeredSamplingFluctuation Omega2 p
            (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1)) := by
  unfold quadraticMiddleIndexDistinctCenteredCoefficientMatrix matrixEntrySum
  simp only [csf_apply, quadraticMiddleIndexDistinctKernelSquareBaseMatrix, Prod.mk.eta]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  by_cases h : w = w1
  · simp [h]
  · rw [if_neg h, if_neg h]; ring
