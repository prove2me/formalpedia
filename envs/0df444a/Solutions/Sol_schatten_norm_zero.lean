-- Prove2me | solution 1 for schatten_norm_zero
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-21T17:41:13.6618+00:00
-- url     : https://prove2.me/submissions/62273423-4115-4644-bd47-ff65d69aa1fa

import Definitions.Def_matrix_completion_schatten

open MatrixCompletion
open scoped BigOperators

theorem solution :
    ∀ {n₁ n₂ : ℕ} (q : ℝ), q ≠ 0 →
      schattenNorm q (0 : Matrix (Fin n₁) (Fin n₂) ℝ) = 0 := by
  intro n₁ n₂ q hq
  unfold schattenNorm
  have h0 : (Matrix.toEuclideanLin (0 : Matrix (Fin n₁) (Fin n₂) ℝ)) = 0 := by simp
  rw [h0, LinearMap.singularValues_zero]
  have hsum : (∑ _k : Fin n₂, Real.rpow ((0 : ℕ →₀ ℝ) _k) q) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    simp [Real.zero_rpow hq]
  rw [hsum]
  exact Real.zero_rpow (inv_ne_zero hq)
