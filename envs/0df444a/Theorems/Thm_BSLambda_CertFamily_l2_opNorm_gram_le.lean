-- Prove2me | Theorems.Thm_BSLambda_CertFamily_l2_opNorm_gram_le
-- name    : BSLambda.CertFamily.l2_opNorm_gram_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:20:03.794095+00:00
-- url     : https://prove2.me/theorems/71ef1b9b-18a0-4e31-b9bd-9a3a9cecba79
-- title:
--   Cert Family: l2 op Norm gram le
-- statement:
--   The triangle inequality on the splitting `G = D + R + Rᵀ` (Section 11.3).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertUnion.lean#L258-L262
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertUnion.lean#L258-L262

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

theorem BSLambda.CertFamily.l2_opNorm_gram_le : ‖gram F.ind‖ ≤ (F.c : ℝ) + 2 * F.offBound := by sorry
