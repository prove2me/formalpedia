-- Prove2me | Theorems.Thm_DeletionCode_SignedSupport_bubble_positive_value
-- name    : DeletionCode.SignedSupport.bubble_positive_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:13:34.519272+00:00
-- url     : https://prove2.me/theorems/039a82b7-a7dd-4ac3-9341-710e6f12c237
-- title:
--   Signed Support: bubble positive value
-- statement:
--   The Signed Support construction uses the bubble positive value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedSupport.lean#L158-L167
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedSupport.lean#L158-L167

import Definitions.Def_DeletionCode_SupportComponents
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Definitions.Def_DeletionCode_SignedSupport
set_option autoImplicit true
open DeletionCode DeletionCode.SignedSupport
open Windows RootSelection
open scoped BigOperators

theorem DeletionCode.SignedSupport.bubble_positive_value {B : Type*} (F : Family B) (L : ℕ)
    (H : BubbleGeometry F L) (b : B) (g : Gram L)
    (hp : g ∈ windowSet (F.path b true) L (F.extra b true)) :
    bubbleSpectrum F L b g = 1 := by sorry
