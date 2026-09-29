-- Prove2me | solution 1 for left_singular_projection_matrix_is_star_projection
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-22T01:20:01.208631+00:00
-- url     : https://prove2.me/submissions/2c8f8516-8ef1-4056-99b7-de932dc9abe1

import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

open MatrixCompletion

open scoped Matrix.Norms.L2Operator

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) :
    @IsStarProjection (Matrix (Fin n₁) (Fin n₁) ℝ)
      Matrix.instMulOfFintypeOfAddCommMonoid Matrix.instStar
      (fun i a : Fin n₁ => ∑ k : Fin r, S.u k i * S.u k a :
        Matrix (Fin n₁) (Fin n₁) ℝ) := by
  constructor
  · ext i j
    calc
      (∑ a : Fin n₁,
          (∑ k : Fin r, S.u k i * S.u k a) *
            (∑ l : Fin r, S.u l a * S.u l j))
          =
          ∑ k : Fin r, ∑ l : Fin r,
            S.u k i * S.u l j * (∑ a : Fin n₁, S.u k a * S.u l a) := by
            simp_rw [Finset.sum_mul, Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro k _hk
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro l _hl
            refine Finset.sum_congr rfl ?_
            intro a _ha
            ring
      _ = ∑ k : Fin r, ∑ l : Fin r,
            S.u k i * S.u l j * (if k = l then 1 else 0) := by
            simp [S.u_orthonormal]
      _ = ∑ k : Fin r, S.u k i * S.u k j := by
            simp
  · ext i j
    change star (∑ k : Fin r, S.u k j * S.u k i) = ∑ k : Fin r, S.u k i * S.u k j
    simp [mul_comm]
