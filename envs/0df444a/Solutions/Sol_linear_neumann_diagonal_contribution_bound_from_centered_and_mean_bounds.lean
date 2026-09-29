-- Prove2me | solution 1 for linear_neumann_diagonal_contribution_bound_from_centered_and_mean_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-20T19:03:22.255306+00:00
-- url     : https://prove2.me/submissions/cd7c6848-ffe4-46b8-9c21-c8a098560082

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped Classical BigOperators

private theorem spectralNorm_add_le {n₁ n₂ : Nat} (A B : Matrix (Fin n₁) (Fin n₂) ℝ) :
    spectralNorm (A + B) ≤ spectralNorm A + spectralNorm B := by
  unfold spectralNorm
  rw [map_add, map_add]
  exact norm_add_le _ _

private theorem sum_coord_apply {n₁ n₂ : Nat} (f : Fin n₁ × Fin n₂ → ℝ) (i : Fin n₁) (j : Fin n₂) :
    (∑ w : Fin n₁ × Fin n₂, f w • coordinateMatrix w.1 w.2) i j = f (i, j) := by
  rw [Matrix.sum_apply, Finset.sum_eq_single (i, j)]
  · simp [coordinateMatrix, Matrix.smul_apply]
  · intro w _ hw
    have hne : ¬ (i = w.1 ∧ j = w.2) := fun ⟨hi, hj⟩ => hw (Prod.ext hi.symm hj.symm)
    simp only [Matrix.smul_apply, coordinateMatrix, if_neg hne, smul_eq_mul, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Omega : Finset (Fin n₁ × Fin n₂))
    (p Ccenter Cmean lam : ℝ) :
    spectralNorm (linearNeumannDiagonalCenteredContribution Omega S p) ≤
      Ccenter * Real.rpow lam (-1) →
    spectralNorm (linearNeumannDiagonalMeanContribution S p) ≤
      Cmean * Real.rpow lam (-1) →
    spectralNorm (linearNeumannDiagonalContribution Omega S p) ≤
      (Ccenter + Cmean) * Real.rpow lam (-1) := by
  intro hC hM
  have heq : linearNeumannDiagonalContribution Omega S p =
      linearNeumannDiagonalCenteredContribution Omega S p +
        linearNeumannDiagonalMeanContribution S p := by
    unfold linearNeumannDiagonalContribution linearNeumannDiagonalCenteredContribution
      linearNeumannDiagonalMeanContribution
    ext i j
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.smul_apply,
      sum_coord_apply, sum_coord_apply, sum_coord_apply]
    unfold centeredIndicator
    by_cases hm : (i, j) ∈ Omega
    · simp only [hm, if_true]; ring
    · simp only [hm, if_false]; ring
  rw [heq]
  calc spectralNorm (linearNeumannDiagonalCenteredContribution Omega S p +
          linearNeumannDiagonalMeanContribution S p)
      ≤ spectralNorm (linearNeumannDiagonalCenteredContribution Omega S p) +
          spectralNorm (linearNeumannDiagonalMeanContribution S p) := spectralNorm_add_le _ _
    _ ≤ Ccenter * Real.rpow lam (-1) + Cmean * Real.rpow lam (-1) := add_le_add hC hM
    _ = (Ccenter + Cmean) * Real.rpow lam (-1) := by ring
