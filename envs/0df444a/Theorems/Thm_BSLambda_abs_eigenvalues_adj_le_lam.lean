-- Prove2me | Theorems.Thm_BSLambda_abs_eigenvalues_adj_le_lam
-- name    : BSLambda.abs_eigenvalues_adj_le_lam
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:09:17.687831+00:00
-- url     : https://prove2.me/theorems/5cdda396-c09f-44b3-9275-b7c50b211415
-- title:
--   BSLambda: abs eigenvalues adj le lam
-- statement:
--   Every eigenvalue of `A_f` is at most `lambda(f)` in absolute value.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/OpNorm.lean#L87-L97
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/OpNorm.lean#L87-L97

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Bipartite
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix Matrix.Norms.L2Operator
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BSLambda.abs_eigenvalues_adj_le_lam (f : Input V → Bool) (i : Input V) :
    |(isHermitian_adj f).eigenvalues i| ≤ lam f := by sorry
