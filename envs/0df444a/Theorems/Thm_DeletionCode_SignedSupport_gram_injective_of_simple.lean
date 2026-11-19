-- Prove2me | Theorems.Thm_DeletionCode_SignedSupport_gram_injective_of_simple
-- name    : DeletionCode.SignedSupport.gram_injective_of_simple
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:08:07.756003+00:00
-- url     : https://prove2.me/theorems/7e7188e4-a6c6-4c04-b503-8d96f6d896b3
-- title:
--   Signed Support: gram injective of simple
-- statement:
--   The Signed Support construction uses the gram injective of simple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedSupport.lean#L79-L88
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedSupport.lean#L79-L88

import Definitions.Def_DeletionCode_SupportComponents
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Definitions.Def_DeletionCode_SignedSupport
set_option autoImplicit true
open DeletionCode DeletionCode.SignedSupport
open Windows RootSelection
open scoped BigOperators

theorem DeletionCode.SignedSupport.gram_injective_of_simple {B : Type*} (F : Family B) (L : ℕ)
    (H : BubbleGeometry F L) (b : B) (side : Bool) :
    Function.Injective (fun i : Fin (F.extra b side + 1) => gram (F.path b side) L i.val) := by sorry
