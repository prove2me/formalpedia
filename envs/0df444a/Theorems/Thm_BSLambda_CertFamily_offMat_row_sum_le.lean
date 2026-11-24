-- Prove2me | Theorems.Thm_BSLambda_CertFamily_offMat_row_sum_le
-- name    : BSLambda.CertFamily.offMat_row_sum_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:20:11.460502+00:00
-- url     : https://prove2.me/theorems/e3d03a05-85f1-41f5-a87d-b5eec571bdfa
-- title:
--   Cert Family: off Mat row sum le
-- statement:
--   Every row sum of the oriented part is at most `A (c - 1)`: the entries are at most one,
--   so the sum is at most the count of `card_offMat_row_le` (Section 11.3).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertUnion.lean#L225-L228
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/CertUnion.lean#L225-L228

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

theorem BSLambda.CertFamily.offMat_row_sum_le (x : Ones F.ind) :
    ∑ y, F.offMat x y ≤ ((F.A * (F.c - 1) : ℕ) : ℝ) := by sorry
