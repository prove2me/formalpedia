-- Prove2me | Theorems.Thm_DeletionCode_SignedSupport_bubble_support_iff
-- name    : DeletionCode.SignedSupport.bubble_support_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:10:25.211088+00:00
-- url     : https://prove2.me/theorems/1cd17a98-7d0c-43b2-9452-cecdfecc0ff9
-- title:
--   Signed Support: bubble support iff
-- statement:
--   The Signed Support construction uses the bubble support iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedSupport.lean#L169-L187
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedSupport.lean#L169-L187

import Definitions.Def_DeletionCode_SupportComponents
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Definitions.Def_DeletionCode_SignedSupport
set_option autoImplicit true
open DeletionCode DeletionCode.SignedSupport
open Windows RootSelection
open scoped BigOperators

theorem DeletionCode.SignedSupport.bubble_support_iff {B : Type*} (F : Family B) (L : ℕ)
    (H : BubbleGeometry F L) (b : B) (g : Gram L) :
    bubbleSpectrum F L b g ≠ 0 ↔ HasGram F L b g := by sorry
