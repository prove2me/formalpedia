-- Prove2me | Theorems.Thm_BSLambda_CertFamily_gram_eq_add
-- name    : BSLambda.CertFamily.gram_eq_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:18:56.728736+00:00
-- url     : https://prove2.me/theorems/5c0b8d4a-4a41-4220-961d-b6df2cc0294a
-- title:
--   Cert Family: gram eq add
-- statement:
--   The splitting `G = D + R + Rᵀ` of the Gram matrix (Section 11.3).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertUnion.lean#L128-L135
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertUnion.lean#L128-L135

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_GramClass
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertUnion
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.CertFamily
open scoped Matrix Matrix.Norms.L2Operator
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
variable (F : CertFamily V ι)

theorem BSLambda.CertFamily.gram_eq_add : gram F.ind = F.diagMat + F.offMat + F.offMatᵀ := by sorry
