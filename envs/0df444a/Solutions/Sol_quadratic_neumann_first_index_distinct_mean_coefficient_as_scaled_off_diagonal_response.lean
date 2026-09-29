-- Prove2me | solution 1 for quadratic_neumann_first_index_distinct_mean_coefficient_as_scaled_off_diagonal_response
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-20T18:32:03.542861+00:00
-- url     : https://prove2.me/submissions/6431effe-b1cb-419c-a351-1c1d6b347f52

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped Classical BigOperators

private theorem csf_apply {n₁ n₂ : Nat} (Omega : Finset (Fin n₁ × Fin n₂)) (p : ℝ)
    (X : Matrix (Fin n₁) (Fin n₂) ℝ) (i : Fin n₁) (j : Fin n₂) :
    centeredSamplingFluctuation Omega p X i j
      = p⁻¹ * (centeredIndicator Omega p i j * X i j) := by
  show p⁻¹ * (samplingProjection Omega X i j - p * X i j)
      = p⁻¹ * (centeredIndicator Omega p i j * X i j)
  unfold samplingProjection centeredIndicator
  by_cases hm : (i, j) ∈ Omega
  · simp only [hm, if_true]; ring
  · simp only [hm, if_false]; ring

theorem solution
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (p : ℝ) :
    quadraticFirstIndexDistinctMeanCoefficientMatrix S p =
      p⁻¹ • offDiagonalTangentResponse S (linearNeumannDiagonalBaseMatrix S) := by
  ext i j
  rw [Matrix.smul_apply]
  unfold quadraticFirstIndexDistinctMeanCoefficientMatrix offDiagonalTangentResponse
    linearNeumannDiagonalBaseMatrix tangentDiagonalMultiplier
  congr 1
