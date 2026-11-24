-- Prove2me | Theorems.Thm_BSLambda_CertFamily_l2_opNorm_offMat_transpose_le
-- name    : BSLambda.CertFamily.l2_opNorm_offMat_transpose_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:20:03.920801+00:00
-- url     : https://prove2.me/theorems/b771a913-810b-432c-bb92-68f2d6c51809
-- title:
--   Cert Family: l2 op Norm off Mat transpose le
-- statement:
--   The transpose of `R` obeys the same bound, since transposition preserves the L2 operator
--   norm (Section 11.3).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertUnion.lean#L254-L255
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertUnion.lean#L254-L255

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

theorem BSLambda.CertFamily.l2_opNorm_offMat_transpose_le : ‖F.offMatᵀ‖ ≤ F.offBound := by sorry
