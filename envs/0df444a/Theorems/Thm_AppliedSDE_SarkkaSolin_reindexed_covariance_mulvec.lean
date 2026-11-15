-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_reindexed_covariance_mulvec
-- name    : AppliedSDE.SarkkaSolin.reindexed_covariance_mulvec
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:29:52.878609+00:00
-- url     : https://prove2.me/theorems/ce6641a8-1a18-4bfe-bf6c-b6f85bb8952c
-- title:
--   Reindexed finite covariance matrix-vector product agrees with original action
-- statement:
--   For any finite real square covariance matrix C, vector z and equivalence e from a reindexed finite index set to the original, matrix-vector multiplication after simultaneously reindexing the rows, columns and vector is exactly the original product reindexed by e: (C.submatrix e e).mulVec(z compose e)=(C.mulVec z) compose e. This is the exact index-transport lemma needed to carry an inverse Gaussian-process covariance linear system into a Fin(n+1) sum Fin1 Matrix.fromBlocks system, after which the Schur complement and Kalman innovation formulas apply.
-- source:
--   Mathlib.Data.Matrix.Mul submatrix_mulVec_equiv at pinned commit 0df444a360eaa60ab8c11dca51a86af692955474; Särkkä and Solin (2019), Gaussian process/Kalman block update.

import Mathlib
open Matrix

theorem AppliedSDE.SarkkaSolin.reindexed_covariance_mulvec
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (C : Matrix ι ι ℝ) (e : κ ≃ ι) (z : ι → ℝ) :
    (C.submatrix e e).mulVec (z ∘ e) = (C.mulVec z) ∘ e := by
  sorry
