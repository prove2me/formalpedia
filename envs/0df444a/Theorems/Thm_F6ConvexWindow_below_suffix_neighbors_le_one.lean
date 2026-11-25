-- Prove2me | Theorems.Thm_F6ConvexWindow_below_suffix_neighbors_le_one
-- name    : F6ConvexWindow.below_suffix_neighbors_le_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T10:20:12.46049+00:00
-- url     : https://prove2.me/theorems/4653d7da-de28-45fb-ab79-edca6fbebccc
-- title:
--   F6 Convex Window: below suffix neighbors le one
-- statement:
--   All incomparable neighbors in a Below suffix belong to its first triple.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L354-L375
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L354-L375

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.below_suffix_neighbors_le_one (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    (F : Finset (Finset V)) (hf : ∀ T ∈ F, IsTriple T) {x : V}
    (hx : x ∉ tripleUnion F) (hb : ∀ T ∈ F, Below T x) :
    ((tripleUnion F).filter (IncRel x)).card ≤ 1 := by sorry
