-- Prove2me | Theorems.Thm_BSLambda_lam_sq_le_l2_opNorm_gram
-- name    : BSLambda.lam_sq_le_l2_opNorm_gram
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:05:20.287346+00:00
-- url     : https://prove2.me/theorems/103a6dab-ff6e-4b2a-a39b-857af1ad09cb
-- title:
--   BSLambda: lam sq le l2 op Norm gram
-- statement:
--   `lambda(f)^2 <= ‖K‖`, where `K = M Mᵀ` is the positive-side Gram matrix
--   (Section 11.1 of `bs_lambda.txt`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Bipartite.lean#L190-L193
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Bipartite.lean#L190-L193

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

theorem BSLambda.lam_sq_le_l2_opNorm_gram (f : Input V → Bool) : lam f ^ 2 ≤ ‖gram f‖ := by sorry
