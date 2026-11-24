-- Prove2me | Theorems.Thm_BSLambda_CertFamily_card_offMat_col_le
-- name    : BSLambda.CertFamily.card_offMat_col_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:20:07.731642+00:00
-- url     : https://prove2.me/theorems/3ca1dfc5-52c1-4098-8da8-d46266f284ae
-- title:
--   Cert Family: card off Mat col le
-- statement:
--   Every column of the oriented part has at most `B` nonzero entries: every row index `x`
--   of the column of `y` has a distinct owner, at distance two from `y`, and `listTwo` bounds the
--   number of those (Section 11.3, column bound).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertUnion.lean#L208-L219
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertUnion.lean#L208-L219

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

theorem BSLambda.CertFamily.card_offMat_col_le (y : Ones F.ind) :
    (Finset.univ.filter fun x : Ones F.ind => F.offMat x y ≠ 0).card ≤ F.B := by sorry
