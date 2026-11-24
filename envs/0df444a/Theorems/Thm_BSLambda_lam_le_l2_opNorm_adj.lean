-- Prove2me | Theorems.Thm_BSLambda_lam_le_l2_opNorm_adj
-- name    : BSLambda.lam_le_l2_opNorm_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:58:27.315804+00:00
-- url     : https://prove2.me/theorems/d17ffa03-cfb6-4a79-b23f-6033e930abf8
-- title:
--   BSLambda: lam le l2 op Norm adj
-- statement:
--   `lambda(f)` is at most the L2 operator norm of the adjacency matrix (Section 11.1).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Spectral.lean#L133-L134
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Spectral.lean#L133-L134

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Hermitian
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Spectral
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix Matrix.Norms.L2Operator
variable {V : Type*} [Fintype V]
variable [DecidableEq V]

theorem BSLambda.lam_le_l2_opNorm_adj (f : Input V → Bool) : lam f ≤ ‖adj f‖ := by sorry
