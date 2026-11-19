-- Prove2me | Theorems.Thm_DeletionCode_SignedSupport_pathSpectrum_eq_zero
-- name    : DeletionCode.SignedSupport.pathSpectrum_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:08:04.497568+00:00
-- url     : https://prove2.me/theorems/5d6b1cf0-6be7-4ff5-a9cd-ce90ab93ec32
-- title:
--   Signed Support: path Spectrum eq zero
-- statement:
--   The Signed Support construction uses the path Spectrum eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedSupport.lean#L131-L137
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedSupport.lean#L131-L137

import Definitions.Def_DeletionCode_SupportComponents
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Definitions.Def_DeletionCode_SignedSupport
set_option autoImplicit true
open DeletionCode DeletionCode.SignedSupport
open Windows RootSelection
open scoped BigOperators

theorem DeletionCode.SignedSupport.pathSpectrum_eq_zero (p : Letters) (L D : ℕ) (g : Gram L)
    (hg : g ∉ windowSet p L D) : pathSpectrum p L D g = 0 := by sorry
