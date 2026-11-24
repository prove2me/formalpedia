-- Prove2me | Theorems.Thm_BSLambda_l2_opNorm_adj_le_lam
-- name    : BSLambda.l2_opNorm_adj_le_lam
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:09:25.599083+00:00
-- url     : https://prove2.me/theorems/ef70aba9-7aba-4af9-990e-5efb2fde3e36
-- title:
--   BSLambda: l2 op Norm adj le lam
-- statement:
--   The L2 operator norm of the sensitivity adjacency matrix is at most `lambda(f)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/OpNorm.lean#L100-L101
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/OpNorm.lean#L100-L101

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Bipartite
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix Matrix.Norms.L2Operator
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BSLambda.l2_opNorm_adj_le_lam (f : Input V → Bool) : ‖adj f‖ ≤ lam f := by sorry
