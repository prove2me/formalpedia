-- Prove2me | Theorems.Thm_DeletionCode_SignedSupport_prefix_gram
-- name    : DeletionCode.SignedSupport.prefix_gram
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:14:31.692942+00:00
-- url     : https://prove2.me/theorems/c18af8b6-79ec-4d49-9ecc-2b26c2e1e0d7
-- title:
--   Signed Support: prefix gram
-- statement:
--   The Signed Support construction uses the prefix gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedSupport.lean#L313-L315
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedSupport.lean#L313-L315

import Definitions.Def_DeletionCode_SupportComponents
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Definitions.Def_DeletionCode_SignedSupport
set_option autoImplicit true
open DeletionCode DeletionCode.SignedSupport
open Windows RootSelection
open scoped BigOperators

theorem DeletionCode.SignedSupport.prefix_gram {B : Type*} (F : Family B) (L : ℕ)
    (b : B) (side : Bool) (i : ℕ) :
    gramPrefix (gram (F.path b side) L i) = SupportComponents.vertex F L b side i := by sorry
