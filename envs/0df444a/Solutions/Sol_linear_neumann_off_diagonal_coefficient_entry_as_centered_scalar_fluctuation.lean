-- Prove2me | solution 1 for linear_neumann_off_diagonal_coefficient_entry_as_centered_scalar_fluctuation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-24T14:39:00.090045+00:00
-- url     : https://prove2.me/submissions/89cc0d9b-405f-4dd5-bd37-079897012e52

import Definitions.Def_linear_neumann_offdiag_bernstein

open MatrixCompletion
open scoped BigOperators

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
    (Omega2 : Finset (Fin n₁ × Fin n₂)) (S : SVD M r)
    (p : ℝ) (w : Fin n₁ × Fin n₂) :
    linearNeumannOffDiagonalCoefficientMatrix Omega2 S p w.1 w.2 =
      matrixEntrySum
        (centeredSamplingFluctuation Omega2 p
          (linearNeumannOffDiagonalCoefficientBaseMatrix S w)) := by
  unfold linearNeumannOffDiagonalCoefficientMatrix matrixEntrySum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro u _
  rw [csf_apply]
  simp only [linearNeumannOffDiagonalCoefficientBaseMatrix, Prod.mk.eta]
  by_cases h : u = w
  · simp [h]
  · rw [if_neg h, if_neg h]
    ring
