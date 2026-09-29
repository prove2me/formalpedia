-- Prove2me | solution 1 for quadratic_neumann_first_index_distinct_bound_from_centered_and_mean_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-20T19:13:19.164047+00:00
-- url     : https://prove2.me/submissions/3114414b-a52c-461d-a3d2-855604b9e09f

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped Classical BigOperators

private theorem spectralNorm_add_le {n₁ n₂ : Nat} (A B : Matrix (Fin n₁) (Fin n₂) ℝ) :
    spectralNorm (A + B) ≤ spectralNorm A + spectralNorm B := by
  unfold spectralNorm; rw [map_add, map_add]; exact norm_add_le _ _

private theorem dsum_apply {n₁ n₂ : Nat}
    (f : (Fin n₁ × Fin n₂) → (Fin n₁ × Fin n₂) → ℝ) (i : Fin n₁) (j : Fin n₂) :
    (∑ w1 : Fin n₁ × Fin n₂, ∑ w2 : Fin n₁ × Fin n₂,
        (if w1 = w2 then (0 : Matrix (Fin n₁) (Fin n₂) ℝ)
          else f w1 w2 • coordinateMatrix w1.1 w1.2)) i j
      = ∑ w2 : Fin n₁ × Fin n₂, (if (i, j) = w2 then (0:ℝ) else f (i, j) w2) := by
  rw [Matrix.sum_apply, Finset.sum_eq_single (i, j)]
  · rw [Matrix.sum_apply]
    apply Finset.sum_congr rfl
    intro w2 _
    by_cases h : (i, j) = w2
    · simp [h]
    · simp only [if_neg h, Matrix.smul_apply, smul_eq_mul]
      rw [show coordinateMatrix (i, j).1 (i, j).2 i j = 1 from by simp [coordinateMatrix], mul_one]
  · intro w1 _ hw1
    rw [Matrix.sum_apply]
    apply Finset.sum_eq_zero
    intro w2 _
    have hne : ¬ (i = w1.1 ∧ j = w1.2) := fun ⟨hi, hj⟩ => hw1 (Prod.ext hi.symm hj.symm)
    by_cases h : w1 = w2
    · simp [h]
    · simp only [if_neg h, Matrix.smul_apply, coordinateMatrix, if_neg hne, smul_eq_mul, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

private theorem csq {n₁ n₂ : Nat} (Omega : Finset (Fin n₁ × Fin n₂)) (p : ℝ)
    (a : Fin n₁) (b : Fin n₂) :
    (centeredIndicator Omega p a b) ^ 2
      = (1 - 2 * p) * (centeredIndicator Omega p a b) + p * (1 - p) := by
  unfold centeredIndicator
  by_cases h : (a, b) ∈ Omega
  · simp only [h, if_true]; ring
  · simp only [h, if_false]; ring

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Omega : Finset (Fin n₁ × Fin n₂))
    (p Ccent Cmean lam : ℝ) :
    spectralNorm (quadraticNeumannFirstIndexDistinctCenteredContribution Omega S p) ≤ Ccent * Real.rpow lam (-((3 : ℝ) / 2)) →
    spectralNorm (quadraticNeumannFirstIndexDistinctMeanContribution Omega S p) ≤ Cmean * Real.rpow lam (-((3 : ℝ) / 2)) →
    spectralNorm (quadraticNeumannFirstIndexDistinctContribution Omega S p) ≤ (Ccent + Cmean) * Real.rpow lam (-((3 : ℝ) / 2)) := by
  intro hC hM
  have heq : quadraticNeumannFirstIndexDistinctContribution Omega S p = quadraticNeumannFirstIndexDistinctCenteredContribution Omega S p + quadraticNeumannFirstIndexDistinctMeanContribution Omega S p := by
    unfold quadraticNeumannFirstIndexDistinctContribution quadraticNeumannFirstIndexDistinctCenteredContribution quadraticNeumannFirstIndexDistinctMeanContribution
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, dsum_apply, smul_eq_mul]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w _
    by_cases h : (i, j) = w
    · simp [h]
    · simp only [if_neg h]
      rw [csq Omega p w.1 w.2]
      by_cases hp : p = 0
      · simp [hp]
      · have hpe : p ≠ 0 := hp; field_simp; try ring
  rw [heq]
  calc spectralNorm (quadraticNeumannFirstIndexDistinctCenteredContribution Omega S p + quadraticNeumannFirstIndexDistinctMeanContribution Omega S p)
      ≤ spectralNorm (quadraticNeumannFirstIndexDistinctCenteredContribution Omega S p) + spectralNorm (quadraticNeumannFirstIndexDistinctMeanContribution Omega S p) :=
        spectralNorm_add_le _ _
    _ ≤ Ccent * Real.rpow lam (-((3 : ℝ) / 2)) + Cmean * Real.rpow lam (-((3 : ℝ) / 2)) := add_le_add hC hM
    _ = (Ccent + Cmean) * Real.rpow lam (-((3 : ℝ) / 2)) := by ring
