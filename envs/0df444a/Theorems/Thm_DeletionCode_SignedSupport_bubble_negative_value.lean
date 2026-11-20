-- Prove2me | Theorems.Thm_DeletionCode_SignedSupport_bubble_negative_value
-- name    : DeletionCode.SignedSupport.bubble_negative_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:10:12.922733+00:00
-- url     : https://prove2.me/theorems/222a5f86-13e6-4411-892d-3b4ccf7adba8
-- title:
--   Signed Support: bubble negative value
-- statement:
--   The Signed Support construction uses the bubble negative value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedSupport.lean#L148-L156
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedSupport.lean#L148-L156

import Definitions.Def_DeletionCode_SupportComponents
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Definitions.Def_DeletionCode_SignedSupport
set_option autoImplicit true
open DeletionCode DeletionCode.SignedSupport
open Windows RootSelection
open scoped BigOperators

theorem DeletionCode.SignedSupport.bubble_negative_value {B : Type*} (F : Family B) (L : ℕ)
    (H : BubbleGeometry F L) (b : B) (g : Gram L)
    (hn : g ∈ windowSet (F.path b false) L (F.extra b false)) :
    bubbleSpectrum F L b g = -1 := by sorry
