-- Prove2me | solution 1 for distinct_matrix_subtraction_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-15T15:18:47.401022+00:00
-- url     : https://prove2.me/submissions/1ea0b417-c99f-4e15-910d-cf6247ec4369

import Definitions.Def_matrix_completion_basic

open MatrixCompletion


open MatrixCompletion

theorem solution
    {n₁ n₂ : ℕ} (X M : Matrix (Fin n₁) (Fin n₂) ℝ) :
    X ≠ M → X - M ≠ 0 := by
  intro hne hzero
  apply hne
  ext i j
  have hentry : X i j - M i j = 0 := by
    simpa using congrArg (fun A : Matrix (Fin n₁) (Fin n₂) ℝ => A i j) hzero
  exact sub_eq_zero.mp hentry
