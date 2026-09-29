-- Prove2me | solution 1 for normal_projection_eq_inclusion_exclusion_of_singular_projections
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-22T00:16:48.456493+00:00
-- url     : https://prove2.me/submissions/f97d4f00-35cb-444e-a029-8e22920ede95

import Definitions.Def_matrix_completion_tangent
import Mathlib.Tactic

open MatrixCompletion

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    normalProjection S X =
      X - leftSingularProjection S X - rightSingularProjection S X +
        twoSidedSingularProjection S X := by
  ext i j
  simp [normalProjection, tangentProjection]
  ring
