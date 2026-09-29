-- Prove2me | solution 1 for quadratic_neumann_middle_index_distinct_mean_coefficient_as_centered_scalar_fluctuation
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-20T18:26:41.463946+00:00
-- url     : https://prove2.me/submissions/1441a182-656b-4b26-ada2-756ff287c6c6

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped Classical BigOperators

private theorem csf_apply {n₁ n₂ : Nat} (Omega : Finset (Fin n₁ × Fin n₂)) (p : ℝ)
    (X : Matrix (Fin n₁) (Fin n₂) ℝ) (i : Fin n₁) (j : Fin n₂) :
    centeredSamplingFluctuation Omega p X i j
      = p⁻¹ * (centeredIndicator Omega p i j * X i j) := by
  show (p⁻¹ • (samplingProjection Omega X - p • X)) i j = _
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  unfold samplingProjection centeredIndicator
  by_cases hm : (i, j) ∈ Omega
  · rw [if_pos hm, if_pos hm]; ring
  · rw [if_neg hm, if_neg hm]; ring

theorem solution
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r)
    (p : ℝ) (w1 : Fin n₁ × Fin n₂) :
    quadraticMiddleIndexDistinctMeanCoefficient Omega S p w1 =
      matrixEntrySum
        (centeredSamplingFluctuation Omega p
          (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1)) := by
  unfold quadraticMiddleIndexDistinctMeanCoefficient matrixEntrySum
  simp only [csf_apply, quadraticMiddleIndexDistinctKernelSquareBaseMatrix, Prod.mk.eta]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  by_cases h : w = w1
  · simp [h]
  · rw [if_neg h, if_neg h]; ring
