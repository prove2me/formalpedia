-- Prove2me | Theorems.Thm_BSLambda_CertFamily_offMat_ne_zero_iff
-- name    : BSLambda.CertFamily.offMat_ne_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:15:22.178799+00:00
-- url     : https://prove2.me/theorems/2863df6f-e070-4578-80f0-e7d3b280b47f
-- title:
--   Cert Family: off Mat ne zero iff
-- statement:
--   Reading off the three conditions hidden behind a nonzero entry of the oriented part
--   (Section 11.3).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertUnion.lean#L141-L147
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertUnion.lean#L141-L147

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

theorem BSLambda.CertFamily.offMat_ne_zero_iff {x y : Ones F.ind} :
    F.offMat x y ≠ 0 ↔
      F.owner x ≠ F.owner y ∧ (F.P (F.owner y)).dist x.1 = 1 ∧ gram F.ind x y ≠ 0 := by sorry
