-- Prove2me | Theorems.Thm_BSLambda_exists_top_eigenvector
-- name    : BSLambda.exists_top_eigenvector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:09:25.508206+00:00
-- url     : https://prove2.me/theorems/534046c4-f187-4ef0-8b3a-f657f00db287
-- title:
--   BSLambda: exists top eigenvector
-- statement:
--   The largest eigenvalue of `A_f` is attained by an eigenvector.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/OpNorm.lean#L130-L132
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/OpNorm.lean#L130-L132

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Bipartite
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix Matrix.Norms.L2Operator
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BSLambda.exists_top_eigenvector (f : Input V → Bool) :
    ∃ u : Input V → ℝ, u ≠ 0 ∧ adj f *ᵥ u = lam f • u := by sorry
