-- Prove2me | solution 1 for quadratic_neumann_middle_index_distinct_mean_as_coefficient_sum
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-20T18:37:34.935796+00:00
-- url     : https://prove2.me/submissions/ba91041e-6028-4244-9aed-5bd7857fb64e

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped Classical BigOperators

private theorem sum_coord_apply {n₁ n₂ : Nat} (f : Fin n₁ × Fin n₂ → ℝ) (i : Fin n₁) (j : Fin n₂) :
    (∑ w : Fin n₁ × Fin n₂, f w • coordinateMatrix w.1 w.2) i j = f (i, j) := by
  rw [Matrix.sum_apply, Finset.sum_eq_single (i, j)]
  · simp [coordinateMatrix, Matrix.smul_apply]
  · intro w _ hw
    have hne : ¬ (i = w.1 ∧ j = w.2) := fun ⟨hi, hj⟩ => hw (Prod.ext hi.symm hj.symm)
    simp only [Matrix.smul_apply, coordinateMatrix, if_neg hne, smul_eq_mul, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem solution
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    quadraticNeumannMiddleIndexDistinctMeanContribution Omega S p =
      (p⁻¹ * (1 - p)) •
        ∑ w1 : Fin n₁ × Fin n₂,
          (signMatrix S w1.1 w1.2 *
            quadraticMiddleIndexDistinctMeanCoefficient Omega S p w1) •
            coordinateMatrix w1.1 w1.2 := by
  unfold quadraticNeumannMiddleIndexDistinctMeanContribution
    quadraticMiddleIndexDistinctMeanCoefficient
  ext i j
  rw [Matrix.smul_apply, Matrix.smul_apply]
  rw [show (∑ w1 : Fin n₁ × Fin n₂, ∑ w2 : Fin n₁ × Fin n₂,
        (if w1 = w2 then (0 : Matrix (Fin n₁) (Fin n₂) ℝ) else
          ((1 - p) * centeredIndicator Omega p w2.1 w2.2 * signMatrix S w1.1 w1.2 *
            tangentCoordinateKernel S w1.1 w1.2 w2.1 w2.2 *
              tangentCoordinateKernel S w2.1 w2.2 w1.1 w1.2) •
            coordinateMatrix w1.1 w1.2))
      = ∑ w1 : Fin n₁ × Fin n₂,
          (∑ w2 : Fin n₁ × Fin n₂, if w1 = w2 then (0:ℝ) else
            ((1 - p) * centeredIndicator Omega p w2.1 w2.2 * signMatrix S w1.1 w1.2 *
              tangentCoordinateKernel S w1.1 w1.2 w2.1 w2.2 *
                tangentCoordinateKernel S w2.1 w2.2 w1.1 w1.2)) •
            coordinateMatrix w1.1 w1.2 from by
      apply Finset.sum_congr rfl; intro w1 _
      rw [Finset.sum_smul]
      apply Finset.sum_congr rfl; intro w2 _
      by_cases h : w1 = w2
      · simp [h]
      · simp only [if_neg h]]
  rw [sum_coord_apply, sum_coord_apply]
  have hsum :
      (∑ w2 : Fin n₁ × Fin n₂, if (i, j) = w2 then (0:ℝ) else
        (1 - p) * centeredIndicator Omega p w2.1 w2.2 * signMatrix S i j *
          tangentCoordinateKernel S i j w2.1 w2.2 *
            tangentCoordinateKernel S w2.1 w2.2 i j)
      = ((1 - p) * signMatrix S i j) *
          ∑ w2 : Fin n₁ × Fin n₂, if w2 = (i, j) then (0:ℝ) else
            centeredIndicator Omega p w2.1 w2.2 *
              tangentCoordinateKernel S i j w2.1 w2.2 *
                tangentCoordinateKernel S w2.1 w2.2 i j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w2 _
    by_cases h : (i, j) = w2
    · simp [h]
    · rw [if_neg h, if_neg (Ne.symm h)]; ring
  rw [hsum]; ring
