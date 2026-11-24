-- Prove2me | Theorems.Thm_BSLambda_l2_opNorm_gram
-- name    : BSLambda.l2_opNorm_gram
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:05:15.534804+00:00
-- url     : https://prove2.me/theorems/cf1f3e95-90dc-4651-b898-eb48d16d3862
-- title:
--   BSLambda: l2 op Norm gram
-- statement:
--   The norm of the Gram matrix `K = M Mᵀ` is the square of the norm of `M` (Section 11.1).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Bipartite.lean#L183-L186
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Bipartite.lean#L183-L186

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

theorem BSLambda.l2_opNorm_gram (f : Input V → Bool) : ‖gram f‖ = ‖biadj f‖ * ‖biadj f‖ := by sorry
