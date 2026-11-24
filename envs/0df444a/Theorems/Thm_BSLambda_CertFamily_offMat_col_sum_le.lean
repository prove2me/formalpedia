-- Prove2me | Theorems.Thm_BSLambda_CertFamily_offMat_col_sum_le
-- name    : BSLambda.CertFamily.offMat_col_sum_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:20:02.298925+00:00
-- url     : https://prove2.me/theorems/a6946eda-f059-42b5-b341-6d2668d0d3e6
-- title:
--   Cert Family: off Mat col sum le
-- statement:
--   Every column sum of the oriented part is at most `B`: the entries are at most one, so
--   the sum is at most the count of `card_offMat_col_le` (Section 11.3).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertUnion.lean#L232-L235
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertUnion.lean#L232-L235

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

theorem BSLambda.CertFamily.offMat_col_sum_le (y : Ones F.ind) :
    ∑ x, F.offMat x y ≤ (F.B : ℝ) := by sorry
