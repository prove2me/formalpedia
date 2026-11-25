-- Prove2me | Theorems.Thm_F6ConvexWindow_later_exclusive_above
-- name    : F6ConvexWindow.later_exclusive_above
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:37:52.786854+00:00
-- url     : https://prove2.me/theorems/da5ca760-7398-5ee7-9b3f-19c713e45c5b
-- title:
--   F6 Convex Window: later exclusive above
-- statement:
--   §2: a later-exclusive point is Above the earlier triple.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L41-L52
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L41-L52

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.later_exclusive_above (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    {S T : Finset V} (hs : IsTriple S) (ht : IsTriple T)
    (hST : ideal S ⊆ ideal T) {y : V} (hyT : y ∈ T) (hyS : y ∉ S) : Above S y := by sorry
