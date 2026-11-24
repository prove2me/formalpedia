-- Prove2me | Theorems.Thm_BSLambda_CertFamily_l2_opNorm_offMat_le
-- name    : BSLambda.CertFamily.l2_opNorm_offMat_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:16:01.074931+00:00
-- url     : https://prove2.me/theorems/43c58255-cbaa-4d21-9b1f-6944deeb9bba
-- title:
--   Cert Family: l2 op Norm off Mat le
-- statement:
--   The Schur test applied to `R`, with the row bound `A (c-1)` and the column bound `B`
--   (Section 11.3).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertUnion.lean#L248-L250
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertUnion.lean#L248-L250

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

theorem BSLambda.CertFamily.l2_opNorm_offMat_le : ‖F.offMat‖ ≤ F.offBound := by sorry
