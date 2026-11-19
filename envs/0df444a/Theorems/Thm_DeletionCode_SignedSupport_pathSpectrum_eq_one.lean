-- Prove2me | Theorems.Thm_DeletionCode_SignedSupport_pathSpectrum_eq_one
-- name    : DeletionCode.SignedSupport.pathSpectrum_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:10:09.314034+00:00
-- url     : https://prove2.me/theorems/846ac06a-cdb7-430e-8253-3b551a280358
-- title:
--   Signed Support: path Spectrum eq one
-- statement:
--   The Signed Support construction uses the path Spectrum eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedSupport.lean#L118-L129
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedSupport.lean#L118-L129

import Definitions.Def_DeletionCode_SupportComponents
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Definitions.Def_DeletionCode_SignedSupport
set_option autoImplicit true
open DeletionCode DeletionCode.SignedSupport
open Windows RootSelection
open scoped BigOperators

theorem DeletionCode.SignedSupport.pathSpectrum_eq_one (p : Letters) (L D : ℕ) (g : Gram L)
    (hinj : Function.Injective (fun i : Fin (D + 1) => gram p L i.val))
    (hg : g ∈ windowSet p L D) : pathSpectrum p L D g = 1 := by sorry
