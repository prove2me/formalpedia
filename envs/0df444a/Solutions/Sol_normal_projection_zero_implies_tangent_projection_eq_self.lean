-- Prove2me | solution 1 for normal_projection_zero_implies_tangent_projection_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-15T15:18:48.806611+00:00
-- url     : https://prove2.me/submissions/8def406d-62f6-4c21-8fa1-da084fa21833

import Definitions.Def_matrix_completion_tangent

open MatrixCompletion


open MatrixCompletion

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (H : Matrix (Fin n₁) (Fin n₂) ℝ) :
    normalProjection S H = 0 →
    tangentProjection S H = H := by
  intro hzero
  have hdiff : H - tangentProjection S H = 0 := by
    simpa [normalProjection] using hzero
  exact (sub_eq_zero.mp hdiff).symm
