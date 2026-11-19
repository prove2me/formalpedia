-- Prove2me | Theorems.Thm_DeletionCode_SignedSupport_suffix_gram
-- name    : DeletionCode.SignedSupport.suffix_gram
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:18:19.82218+00:00
-- url     : https://prove2.me/theorems/a18e51f4-6691-4b73-b34f-0a02940da512
-- title:
--   Signed Support: suffix gram
-- statement:
--   The Signed Support construction uses the suffix gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedSupport.lean#L317-L323
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedSupport.lean#L317-L323

import Definitions.Def_DeletionCode_SupportComponents
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Definitions.Def_DeletionCode_SignedSupport
set_option autoImplicit true
open DeletionCode DeletionCode.SignedSupport
open Windows RootSelection
open scoped BigOperators

theorem DeletionCode.SignedSupport.suffix_gram {B : Type*} (F : Family B) (L : ℕ)
    (b : B) (side : Bool) (i : ℕ) :
    gramSuffix (gram (F.path b side) L i) = SupportComponents.vertex F L b side (i + 1) := by sorry
