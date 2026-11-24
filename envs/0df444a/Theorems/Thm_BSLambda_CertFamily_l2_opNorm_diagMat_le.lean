-- Prove2me | Theorems.Thm_BSLambda_CertFamily_l2_opNorm_diagMat_le
-- name    : BSLambda.CertFamily.l2_opNorm_diagMat_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:20:10.283903+00:00
-- url     : https://prove2.me/theorems/532dded2-77bf-4f0a-8c67-f7ca026695bf
-- title:
--   Cert Family: l2 op Norm diag Mat le
-- statement:
--   The diagonal part has operator norm at most the codimension `c`: the L2 operator norm of
--   a diagonal matrix is the supremum norm of its diagonal, and `gram_diag_le` bounds every Gram
--   diagonal entry by `c` (Section 11.3).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertUnion.lean#L240-L244
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertUnion.lean#L240-L244

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

theorem BSLambda.CertFamily.l2_opNorm_diagMat_le : ‖F.diagMat‖ ≤ (F.c : ℝ) := by sorry
