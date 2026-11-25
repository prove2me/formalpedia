-- Prove2me | Theorems.Thm_F6ConvexWindow_ideal_subset_of_card_le
-- name    : F6ConvexWindow.ideal_subset_of_card_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T09:31:06.677767+00:00
-- url     : https://prove2.me/theorems/003f3ee5-cc6d-5c7f-9c84-e909a646d6d5
-- title:
--   F6 Convex Window: ideal subset of card le
-- statement:
--   Ordering the generated ideals by cardinality realizes their nesting order.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L298-L304
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L298-L304

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.ideal_subset_of_card_le (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    {S T : Finset V} (hs : Antichain S) (ht : Antichain T)
    (hsc : S.card = 3) (htc : T.card = 3) (hc : (ideal S).card ≤ (ideal T).card) :
    ideal S ⊆ ideal T := by sorry
