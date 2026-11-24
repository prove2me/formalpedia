-- Prove2me | Theorems.Thm_BSLambda_l2_opNorm_adj_eq_lam
-- name    : BSLambda.l2_opNorm_adj_eq_lam
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:09:23.788418+00:00
-- url     : https://prove2.me/theorems/ffa79e12-8800-41f5-be12-ce4f8f49deca
-- title:
--   BSLambda: l2 op Norm adj eq lam
-- statement:
--   **`lambda(f)` is the L2 operator norm of `A_f`.**  The sensitivity graph is bipartite, so
--   its spectrum is symmetric about `0` and the largest eigenvalue is the spectral radius.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/OpNorm.lean#L105-L106
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/OpNorm.lean#L105-L106

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Bipartite
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix Matrix.Norms.L2Operator
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BSLambda.l2_opNorm_adj_eq_lam (f : Input V → Bool) : ‖adj f‖ = lam f := by sorry
