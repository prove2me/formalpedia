-- Prove2me | solution 1 for quadratic_neumann_all_equal_contribution_bound_from_centered_and_mean_bounds_at_scale
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-30T17:36:51.253906+00:00
-- url     : https://prove2.me/submissions/bcdac75b-ff58-4f7a-8278-875b539701c3

import Definitions.Def_matrix_completion_neumann
import Mathlib.Tactic

open MatrixCompletion

private lemma spectralNorm_add_le
    {n₁ n₂ : ℕ} (X Y : Matrix (Fin n₁) (Fin n₂) ℝ) :
    spectralNorm (X + Y) ≤ spectralNorm X + spectralNorm Y := by
  unfold spectralNorm
  have hlin :
      LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (X + Y)) =
        LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin X) +
          LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Y) := by
    ext v i
    simp [Matrix.toEuclideanLin]
  rw [hlin]
  exact norm_add_le _ _

private lemma sum_smul_coordinateMatrix_apply
    {n₁ n₂ : ℕ} (f : Fin n₁ × Fin n₂ → ℝ) (i : Fin n₁) (j : Fin n₂) :
    (∑ w : Fin n₁ × Fin n₂, f w • coordinateMatrix w.1 w.2) i j =
      f (i, j) := by
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul]
  calc
    ∑ x, f x * coordinateMatrix x.1 x.2 i j
        = f (i, j) * coordinateMatrix (i, j).1 (i, j).2 i j := by
          refine Finset.sum_eq_single
            (s := (Finset.univ : Finset (Fin n₁ × Fin n₂)))
            (f := fun w => f w * coordinateMatrix w.1 w.2 i j) (i, j) ?_ ?_
          · intro w _hw hne
            have hnot : ¬ (i = w.1 ∧ j = w.2) := by
              intro h
              apply hne
              ext <;> simp [h.1, h.2]
            simp [coordinateMatrix, hnot]
          · intro hmem
            simp at hmem
    _ = f (i, j) := by simp [coordinateMatrix]

private lemma centeredIndicator_cube
    {n₁ n₂ : ℕ} (Omega : Finset (Fin n₁ × Fin n₂)) (p : ℝ)
    (i : Fin n₁) (j : Fin n₂) :
    centeredIndicator Omega p i j ^ 3 =
      (1 - 3 * p + 3 * p ^ 2) * centeredIndicator Omega p i j +
        p * (1 - 3 * p + 2 * p ^ 2) := by
  by_cases h : (i, j) ∈ Omega
  · simp [centeredIndicator, h]
    ring
  · simp [centeredIndicator, h]
    ring

private lemma all_equal_decomposition
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Omega : Finset (Fin n₁ × Fin n₂)) (p : ℝ) :
    quadraticNeumannAllEqualContribution Omega S p =
      quadraticNeumannAllEqualCenteredContribution Omega S p +
        quadraticNeumannAllEqualMeanContribution S p := by
  ext i j
  simp [quadraticNeumannAllEqualContribution,
    quadraticNeumannAllEqualCenteredContribution,
    quadraticNeumannAllEqualMeanContribution,
    sum_smul_coordinateMatrix_apply]
  rw [centeredIndicator_cube Omega p i j]
  by_cases hp : p = 0
  · simp [hp]
  · field_simp [hp]

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Omega : Finset (Fin n₁ × Fin n₂))
    (p Ccent Cmean scale : ℝ) :
    spectralNorm (quadraticNeumannAllEqualCenteredContribution Omega S p) ≤
      Ccent * scale →
    spectralNorm (quadraticNeumannAllEqualMeanContribution S p) ≤
      Cmean * scale →
    spectralNorm (quadraticNeumannAllEqualContribution Omega S p) ≤
      (Ccent + Cmean) * scale := by
  intro hcent hmean
  rw [all_equal_decomposition S Omega p]
  calc
    spectralNorm
        (quadraticNeumannAllEqualCenteredContribution Omega S p +
          quadraticNeumannAllEqualMeanContribution S p)
        ≤ spectralNorm (quadraticNeumannAllEqualCenteredContribution Omega S p) +
          spectralNorm (quadraticNeumannAllEqualMeanContribution S p) :=
        spectralNorm_add_le _ _
    _ ≤ Ccent * scale + Cmean * scale := add_le_add hcent hmean
    _ = (Ccent + Cmean) * scale := by ring
