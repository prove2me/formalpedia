-- Prove2me | solution 1 for quadratic_neumann_all_distinct_decoupled_as_outer_centered_fluctuation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T05:21:25.254313+00:00
-- url     : https://prove2.me/submissions/6e86103c-21f4-42d1-a955-0c7ee85a5658

import Definitions.Def_matrix_completion_neumann
import Mathlib.Tactic.Ring

open MatrixCompletion

private lemma centeredSamplingFluctuation_apply_eq
    {n₁ n₂ : Nat} (Omega : Finset (Fin n₁ × Fin n₂)) (p : ℝ)
    (X : Matrix (Fin n₁) (Fin n₂) ℝ) (i : Fin n₁) (j : Fin n₂) :
    centeredSamplingFluctuation Omega p X i j =
      p⁻¹ * centeredIndicator Omega p i j * X i j := by
  by_cases hmem : (i, j) ∈ Omega
  · simp [centeredSamplingFluctuation, samplingProjection, centeredIndicator,
      hmem]
    ring
  · simp [centeredSamplingFluctuation, samplingProjection, centeredIndicator,
      hmem]
    ring

theorem solution
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega1 Omega2 Omega3 : Finset (Fin n₁ × Fin n₂))
    (S : SVD M r) (p : ℝ) :
    quadraticNeumannAllDistinctDecoupledContribution Omega1 Omega2 Omega3 S p =
      centeredSamplingFluctuation Omega1 p
        (quadraticAllDistinctOuterCoefficientMatrix Omega2 Omega3 S p) := by
  ext i j
  rw [centeredSamplingFluctuation_apply_eq]
  simp [quadraticNeumannAllDistinctDecoupledContribution,
    quadraticAllDistinctOuterCoefficientMatrix,
    quadraticAllDistinctMiddleCoefficient,
    quadraticAllDistinctInnerCoefficient, Matrix.sum_apply]
  rw [Finset.sum_eq_single (i, j)]
  · simp
    ring_nf
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w2 _
    by_cases hw2 : w2 = (i, j)
    · simp [hw2]
    · simp [hw2]
      rw [Finset.mul_sum]
      rw [Finset.mul_sum]
      rw [Finset.sum_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w3 _
      by_cases hw3i : w3 = (i, j)
      · simp [hw2, hw3i]
      · by_cases hw32 : w3 = w2
        · subst w3
          simp [hw2]
        · have hi2 : ¬ (i, j) = w2 := fun h => hw2 h.symm
          have hi3 : ¬ (i, j) = w3 := fun h => hw3i h.symm
          have h23 : ¬ w2 = w3 := fun h => hw32 h.symm
          simp [hi2, hw3i, hi3, hw32, h23, coordinateMatrix]
          ring
  · intro w _ hw
    have hneq : ¬(i = w.1 ∧ j = w.2) := by
      intro h
      apply hw
      ext <;> simp [h.1, h.2]
    have hcoord : coordinateMatrix w.1 w.2 i j = 0 := by
      simp [coordinateMatrix, hneq]
    apply Finset.sum_eq_zero
    intro w2 _
    apply Finset.sum_eq_zero
    intro w3 _
    by_cases hw2 : w = w2
    · simp [hw2]
    · by_cases hw3 : w = w3
      · simp [hw3]
      · by_cases hw23 : w2 = w3
        · simp [hw23]
        · simp [hw2, hw3, hw23, hcoord]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ _))
