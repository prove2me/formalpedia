-- Prove2me | Theorems.Thm_F6ConvexWindow_above_prefix_neighbors_le_one
-- name    : F6ConvexWindow.above_prefix_neighbors_le_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T10:19:18.674566+00:00
-- url     : https://prove2.me/theorems/d0c1feeb-5217-58c3-8dd7-5bbbfe941047
-- title:
--   F6 Convex Window: above prefix neighbors le one
-- statement:
--   All incomparable neighbors in an Above prefix belong to its last triple.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L330-L351
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L330-L351

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.above_prefix_neighbors_le_one (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    (F : Finset (Finset V)) (hf : ∀ T ∈ F, IsTriple T) {x : V}
    (hx : x ∉ tripleUnion F) (ha : ∀ T ∈ F, Above T x) :
    ((tripleUnion F).filter (IncRel x)).card ≤ 1 := by sorry
