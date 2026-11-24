-- Prove2me | Theorems.Thm_BSLambda_CertFamily_card_offMat_row_le
-- name    : BSLambda.CertFamily.card_offMat_row_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:19:59.991815+00:00
-- url     : https://prove2.me/theorems/748c6014-c91a-41d9-9ab4-e2e9b24d7413
-- title:
--   Cert Family: card off Mat row le
-- statement:
--   Every row of the oriented part has at most `A (c - 1)` nonzero entries: the row splits
--   into at most `A` slices, one per certificate at distance one from `x`, and
--   `card_offMat_row_slice_le` bounds each slice (Section 11.3, row bound).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertUnion.lean#L185-L203
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertUnion.lean#L185-L203

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

theorem BSLambda.CertFamily.card_offMat_row_le (x : Ones F.ind) :
    (Finset.univ.filter fun y : Ones F.ind => F.offMat x y ≠ 0).card
      ≤ F.A * (F.c - 1) := by sorry
