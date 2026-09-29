-- Prove2me | solution 1 for linear_neumann_diagonal_centered_as_fixed_matrix_fluctuation
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-20T16:33:40.737816+00:00
-- url     : https://prove2.me/submissions/0d275a2c-7c07-40f4-8514-c424d3ec2f88

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

theorem solution
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    linearNeumannDiagonalCenteredContribution Omega S p =
      (p⁻¹ * (1 - 2 * p)) •
        centeredSamplingFluctuation Omega p
          (linearNeumannDiagonalBaseMatrix S) := by
  ext i j
  unfold linearNeumannDiagonalCenteredContribution
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  rw [Finset.sum_eq_single (i, j)]
  · have h1 : coordinateMatrix (i, j).1 (i, j).2 i j = 1 := by simp [coordinateMatrix]
    rw [h1, csf_apply]
    simp only [linearNeumannDiagonalBaseMatrix, tangentDiagonalMultiplier, centeredIndicator]
    by_cases hm : (i, j) ∈ Omega
    · simp only [hm, if_true]; ring
    · simp only [hm, if_false]; ring
  · intro w _ hw
    have hne : ¬ (i = w.1 ∧ j = w.2) := fun ⟨hi, hj⟩ => hw (Prod.ext hi.symm hj.symm)
    simp only [coordinateMatrix, if_neg hne, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h
