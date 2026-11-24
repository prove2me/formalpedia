-- Prove2me | Theorems.Thm_BSLambda_lam_le_of_sensAt_le
-- name    : BSLambda.lam_le_of_sensAt_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:09:44.677078+00:00
-- url     : https://prove2.me/theorems/eb8140c1-5c05-4afe-a2a8-f1e53761f08f
-- title:
--   BSLambda: lam le of sens At le
-- statement:
--   A bound on the sensitivity of `f` bounds `lambda(f)`: the adjacency matrix has nonnegative
--   entries and all its row sums are at most `k`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/OpNorm.lean#L152-L157
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/OpNorm.lean#L152-L157

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Bipartite
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix Matrix.Norms.L2Operator
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BSLambda.lam_le_of_sensAt_le {f : Input V → Bool} {k : ℝ} (hk : 0 ≤ k)
    (hs : ∀ x, (sensAt f x : ℝ) ≤ k) : lam f ≤ k := by sorry
