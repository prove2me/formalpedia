-- Prove2me | solution 1 for linear_neumann_off_diagonal_coefficient_as_off_diagonal_response
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-20T16:33:02.202562+00:00
-- url     : https://prove2.me/submissions/d1f98458-5822-4ad9-859d-95bcc1892203

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped Classical BigOperators

theorem csf_apply {n₁ n₂ : Nat} (Omega : Finset (Fin n₁ × Fin n₂)) (p : ℝ)
    (X : Matrix (Fin n₁) (Fin n₂) ℝ) (i : Fin n₁) (j : Fin n₂) :
    centeredSamplingFluctuation Omega p X i j
      = p⁻¹ * (centeredIndicator Omega p i j * X i j) := by
  unfold centeredSamplingFluctuation
  rw [Matrix.smul_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
  unfold centeredIndicator samplingProjection
  by_cases hm : (i, j) ∈ Omega
  · simp only [hm, if_true]; ring
  · simp only [hm, if_false]; ring

theorem solution {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega2 : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    linearNeumannOffDiagonalCoefficientMatrix Omega2 S p =
      offDiagonalTangentResponse S
        (centeredSamplingFluctuation Omega2 p (signMatrix S)) := by
  ext i j
  unfold linearNeumannOffDiagonalCoefficientMatrix offDiagonalTangentResponse
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hw : w = (i, j)
  · simp [hw]
  · rw [if_neg hw, if_neg hw, csf_apply]
    ring
