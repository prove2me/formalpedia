-- Prove2me | Theorems.Thm_BSLambda_CertFamily_diagMat_apply
-- name    : BSLambda.CertFamily.diagMat_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:17:45.073798+00:00
-- url     : https://prove2.me/theorems/a9f4435d-8290-4e44-a67f-38efb28fe261
-- title:
--   Cert Family: diag Mat apply
-- statement:
--   The defining formula for an entry of the diagonal part (Section 11.3).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertUnion.lean#L72-L74
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertUnion.lean#L72-L74

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

theorem BSLambda.CertFamily.diagMat_apply (x y : Ones F.ind) :
    F.diagMat x y = if x = y then gram F.ind x x else 0 := by sorry
