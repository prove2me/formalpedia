-- Prove2me | solution 1 for success_prob_eq_fixed_cardinality_event_prob
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-15T15:18:47.736631+00:00
-- url     : https://prove2.me/submissions/7ff8a822-cd18-4085-ab42-7eed7ee5026a

import Definitions.Def_matrix_completion_fixed_cardinality

open MatrixCompletion


open MatrixCompletion

theorem solution
    {n₁ n₂ : ℕ} (m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ) :
    successProb m M =
      fixedCardinalityEventProb m (fun Omega => IsUniqueMinimizer Omega M) := by
  rfl
