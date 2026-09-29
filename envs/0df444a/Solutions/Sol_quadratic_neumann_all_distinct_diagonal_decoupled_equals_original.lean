-- Prove2me | solution 1 for quadratic_neumann_all_distinct_diagonal_decoupled_equals_original
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-20T15:45:05.072829+00:00
-- url     : https://prove2.me/submissions/eb05108a-8109-4dfd-9cb4-b18de4fc2c1f

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem solution
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    quadraticNeumannAllDistinctDecoupledContribution Omega Omega Omega S p =
      quadraticNeumannAllDistinctContribution Omega S p := by
  rfl
