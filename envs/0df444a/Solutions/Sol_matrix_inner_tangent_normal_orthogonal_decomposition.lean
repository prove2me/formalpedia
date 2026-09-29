-- Prove2me | solution 1 for matrix_inner_tangent_normal_orthogonal_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-22T02:08:36.132323+00:00
-- url     : https://prove2.me/submissions/82f73b1d-5609-4c8c-9fc0-023999b72d3e

import Definitions.Def_tangent_projection_algebra
open MatrixCompletion
open scoped BigOperators

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Y H : Matrix (Fin n₁) (Fin n₂) ℝ) :
    matrixInner Y H =
      matrixInner (tangentProjection S Y) (tangentProjection S H) +
        matrixInner (normalProjection S Y) (normalProjection S H) := by
  have hN : ∀ Z : RealMatrix n₁ n₂, normalProjection S Z = Z - tangentProjection S Z := fun _ => rfl
  rw [hN Y, hN H]
  rw [TangentAlgebra.inner_sub_left, TangentAlgebra.inner_sub_right,
    TangentAlgebra.inner_sub_right]
  have hsa : matrixInner (tangentProjection S Y) H
      = matrixInner Y (tangentProjection S H) := TangentAlgebra.tangent_selfadjoint S Y H
  have hTT : matrixInner (tangentProjection S Y) (tangentProjection S H)
      = matrixInner Y (tangentProjection S H) := by
    rw [TangentAlgebra.tangent_selfadjoint S Y (tangentProjection S H),
      TangentAlgebra.tangent_idem S H]
  rw [hsa, hTT]
  ring
