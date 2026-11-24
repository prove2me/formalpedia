-- Prove2me | Theorems.Thm_BSLambda_gram_isHermitian
-- name    : BSLambda.gram_isHermitian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:10:35.457141+00:00
-- url     : https://prove2.me/theorems/e357858f-6366-45a1-aefd-2632cb220db2
-- title:
--   BSLambda: gram is Hermitian
-- statement:
--   The Gram matrix `K = M Mᵀ` of Section 11.1 is symmetric.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Bipartite.lean#L140-L142
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Bipartite.lean#L140-L142

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

theorem BSLambda.gram_isHermitian (f : Input V → Bool) : (gram f).IsHermitian := by sorry
