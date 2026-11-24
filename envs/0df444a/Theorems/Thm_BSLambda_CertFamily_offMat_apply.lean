-- Prove2me | Theorems.Thm_BSLambda_CertFamily_offMat_apply
-- name    : BSLambda.CertFamily.offMat_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:15:19.919434+00:00
-- url     : https://prove2.me/theorems/c1652dfa-0147-45df-a170-2aa5b5caed62
-- title:
--   Cert Family: off Mat apply
-- statement:
--   The defining formula for an entry of the oriented part (Section 11.3).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertUnion.lean#L77-L80
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertUnion.lean#L77-L80

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

theorem BSLambda.CertFamily.offMat_apply (x y : Ones F.ind) :
    F.offMat x y =
      if F.owner x ≠ F.owner y ∧ (F.P (F.owner y)).dist x.1 = 1 then gram F.ind x y else 0 := by sorry
