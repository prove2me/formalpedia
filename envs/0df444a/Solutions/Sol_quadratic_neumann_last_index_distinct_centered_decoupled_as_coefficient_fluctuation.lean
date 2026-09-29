-- Prove2me | solution 1 for quadratic_neumann_last_index_distinct_centered_decoupled_as_coefficient_fluctuation
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-20T18:20:00.494894+00:00
-- url     : https://prove2.me/submissions/318ce2fa-65c7-4d67-a2d8-ed27a37c41f0

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
    (Omega1 Omega3 : Finset (Fin n₁ × Fin n₂)) (S : SVD M r)
    (p : ℝ) :
    quadraticNeumannLastIndexDistinctCenteredDecoupledContribution
        Omega1 Omega3 S p =
      (p⁻¹ * (1 - 2 * p)) •
        centeredSamplingFluctuation Omega1 p
          (quadraticLastIndexDistinctCenteredCoefficientMatrix Omega3 S p) := by
  ext i j
  rw [Matrix.smul_apply, csf_apply]
  unfold quadraticNeumannLastIndexDistinctCenteredDecoupledContribution
    quadraticLastIndexDistinctCenteredCoefficientMatrix
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    apply_ite (f := fun X : Matrix (Fin n₁) (Fin n₂) ℝ => X i j), Matrix.zero_apply]
  rw [Finset.sum_eq_single (i, j)]
  · simp only [show coordinateMatrix (i, j).1 (i, j).2 i j = 1 from by simp [coordinateMatrix],
      mul_one]
    have hsum :
        (∑ w3 : Fin n₁ × Fin n₂, if (i, j) = w3 then (0:ℝ) else
          (1 - 2 * p) * centeredIndicator Omega1 p i j *
            centeredIndicator Omega3 p w3.1 w3.2 * signMatrix S w3.1 w3.2 *
              tangentCoordinateKernel S w3.1 w3.2 i j *
                tangentCoordinateKernel S i j i j)
        = ((1 - 2 * p) * centeredIndicator Omega1 p i j) *
            ∑ w3 : Fin n₁ × Fin n₂, if w3 = (i, j) then (0:ℝ) else
              centeredIndicator Omega3 p w3.1 w3.2 * signMatrix S w3.1 w3.2 *
                tangentCoordinateKernel S w3.1 w3.2 i j *
                  tangentCoordinateKernel S i j i j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w3 _
      by_cases h : (i, j) = w3
      · simp [h]
      · rw [if_neg h, if_neg (Ne.symm h)]; ring
    rw [hsum]; ring
  · intro w1 _ hw1
    have hne : ¬ (i = w1.1 ∧ j = w1.2) := fun ⟨hi, hj⟩ => hw1 (Prod.ext hi.symm hj.symm)
    have hcoord : coordinateMatrix w1.1 w1.2 i j = 0 := by
      simp only [coordinateMatrix, if_neg hne]
    apply Finset.sum_eq_zero
    intro w3 _
    rw [hcoord, mul_zero, ite_self]
  · intro h
    exact absurd (Finset.mem_univ _) h
