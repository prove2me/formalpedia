-- Prove2me | Theorems.Thm_F6ConvexWindow_outsider_neighbors_le_two
-- name    : F6ConvexWindow.outsider_neighbors_le_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:20:01.487884+00:00
-- url     : https://prove2.me/theorems/7ac1e129-5a9d-5af2-bd44-da90a16c1f63
-- title:
--   F6 Convex Window: outsider neighbors le two
-- statement:
--   §4, equation (4): any vertex outside the triple union has at most two neighbors in it.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L378-L407
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L378-L407

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.outsider_neighbors_le_two (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    (F : Finset (Finset V)) (hf : ∀ T ∈ F, IsTriple T) {x : V}
    (hx : x ∉ tripleUnion F) : ((tripleUnion F).filter (IncRel x)).card ≤ 2 := by sorry
