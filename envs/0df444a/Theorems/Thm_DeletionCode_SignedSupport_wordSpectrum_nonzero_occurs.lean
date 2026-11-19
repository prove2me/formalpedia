-- Prove2me | Theorems.Thm_DeletionCode_SignedSupport_wordSpectrum_nonzero_occurs
-- name    : DeletionCode.SignedSupport.wordSpectrum_nonzero_occurs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:10:51.929196+00:00
-- url     : https://prove2.me/theorems/bbc3be54-10dd-4d96-a29f-caeddf95c0c4
-- title:
--   Signed Support: word Spectrum nonzero occurs
-- statement:
--   The Signed Support construction uses the word Spectrum nonzero occurs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedSupport.lean#L258-L266
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedSupport.lean#L258-L266

import Definitions.Def_DeletionCode_SupportComponents
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Definitions.Def_DeletionCode_SignedSupport
set_option autoImplicit true
open DeletionCode DeletionCode.SignedSupport
open Windows RootSelection
open scoped BigOperators

theorem DeletionCode.SignedSupport.wordSpectrum_nonzero_occurs (x : Letters) (n L : ℕ) (g : Gram L)
    (h : wordSpectrum x n L g ≠ 0) : ∃ a, a + L ≤ n ∧ gram x L a = g := by sorry
