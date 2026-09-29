-- Prove2me | solution 1 for singular_projection_inclusion_exclusion_eq_left_right_complement_mul
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-22T04:09:46.655369+00:00
-- url     : https://prove2.me/submissions/e4132fa5-2007-4a4a-bbf2-d1e2124df2f8

import Definitions.Def_matrix_completion_tangent
import Mathlib.Tactic

open MatrixCompletion

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    X - leftSingularProjection S X - rightSingularProjection S X +
        twoSidedSingularProjection S X =
      (1 - Matrix.of (fun i a : Fin n₁ => ∑ k : Fin r, S.u k i * S.u k a)) *
        X *
        (1 - Matrix.of (fun b j : Fin n₂ => ∑ k : Fin r, S.v k b * S.v k j)) := by
  ext i j
  simp [leftSingularProjection, rightSingularProjection, twoSidedSingularProjection,
    Matrix.mul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply,
    Finset.sum_sub_distrib, sub_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  ring_nf
  simp_rw [Finset.sum_sub_distrib]
  have hdelta1 : (∑ x : Fin n₂, X i x * (if x = j then (1 : ℝ) else 0)) = X i j := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  have hdelta2 :
      (∑ x : Fin n₂, ∑ x_1 : Fin n₁, ∑ x_2 : Fin r,
        S.u x_2 i * S.u x_2 x_1 * X x_1 x * (if x = j then (1 : ℝ) else 0)) =
        ∑ x_1 : Fin n₁, ∑ x_2 : Fin r, S.u x_2 i * S.u x_2 x_1 * X x_1 j := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  rw [hdelta1, hdelta2]
  rw [show (∑ x : Fin n₁, ∑ x_1 : Fin r, S.u x_1 i * S.u x_1 x * X x j) =
      ∑ x_1 : Fin r, ∑ x : Fin n₁, S.u x_1 i * S.u x_1 x * X x j by
    rw [Finset.sum_comm]]
  ring_nf
  have htriple :
      (∑ x : Fin n₁, ∑ x_1 : Fin n₂, ∑ x_2 : Fin r,
        (X x x_1 * ∑ x : Fin r, S.v x x_1 * S.v x j) * S.u x_2 i * S.u x_2 x) =
      (∑ x : Fin n₂, ∑ x_1 : Fin n₁, ∑ x_2 : Fin r,
        (∑ x_3 : Fin r, S.v x_3 x * S.v x_3 j) * X x_1 x * S.u x_2 i * S.u x_2 x_1) := by
    rw [Finset.sum_comm]
    simp [mul_left_comm, mul_comm]
  rw [htriple]
  ring_nf
