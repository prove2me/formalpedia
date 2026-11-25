-- Prove2me | Theorems.Thm_F6ConvexWindow_triple_split
-- name    : F6ConvexWindow.triple_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:31:33.109251+00:00
-- url     : https://prove2.me/theorems/a1d0c4ba-9000-573b-a6cf-4e9e8f9cbe55
-- title:
--   F6 Convex Window: triple split
-- statement:
--   §7a: an outside point is below at least two or above at least two triple members.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L170-L209
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L170-L209

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.triple_split (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    {T : Finset V} (ht : Antichain T) (hc : T.card = 3) {x : V} (hx : x ∉ T) :
    Below T x ∨ Above T x := by sorry
