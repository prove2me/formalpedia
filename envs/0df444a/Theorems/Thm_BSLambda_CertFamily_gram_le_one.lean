-- Prove2me | Theorems.Thm_BSLambda_CertFamily_gram_le_one
-- name    : BSLambda.CertFamily.gram_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:17:37.726541+00:00
-- url     : https://prove2.me/theorems/153908e7-bd64-4176-9749-9852297315dc
-- title:
--   Cert Family: gram le one
-- statement:
--   Distinct positive inputs have at most one common negative neighbour: the two candidates
--   are the midpoints `x^p` and `x^q`, and by `ind_flipSet_singleton_eq_true_or` at most one of
--   them is negative (Section 11.2).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/GramClass.lean#L213-L225
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/GramClass.lean#L213-L225

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertFamily
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_GramClass
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*} [Fintype V] [DecidableEq V]
open BSLambda.CertFamily
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (F : CertFamily V ι)

theorem BSLambda.CertFamily.gram_le_one {x y : Ones F.ind} (hxy : x ≠ y) : gram F.ind x y ≤ 1 := by sorry
