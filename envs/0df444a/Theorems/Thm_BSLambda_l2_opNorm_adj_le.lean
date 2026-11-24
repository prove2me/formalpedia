-- Prove2me | Theorems.Thm_BSLambda_l2_opNorm_adj_le
-- name    : BSLambda.l2_opNorm_adj_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:05:17.883475+00:00
-- url     : https://prove2.me/theorems/371a397d-e7bf-4bda-981e-0c44771e53df
-- title:
--   BSLambda: l2 op Norm adj le
-- statement:
--   The L2 operator norm of `A_f` is bounded by that of its off-diagonal block `M`
--   (Section 11.1 of `bs_lambda.txt`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Bipartite.lean#L168-L180
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Bipartite.lean#L168-L180

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Spectral
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_SchurTest
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Bipartite
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix Matrix.Norms.L2Operator
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BSLambda.l2_opNorm_adj_le (f : Input V → Bool) : ‖adj f‖ ≤ ‖biadj f‖ := by sorry
