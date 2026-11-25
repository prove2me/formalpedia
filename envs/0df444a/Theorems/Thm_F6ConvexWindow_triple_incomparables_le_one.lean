-- Prove2me | Theorems.Thm_F6ConvexWindow_triple_incomparables_le_one
-- name    : F6ConvexWindow.triple_incomparables_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:31:28.792613+00:00
-- url     : https://prove2.me/theorems/d7de8195-5bf7-5666-89a5-23ddd91ab2c9
-- title:
--   F6 Convex Window: triple incomparables le one
-- statement:
--   At most one element of a triple can be incomparable with an outside point.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L138-L164
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L138-L164

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.triple_incomparables_le_one (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    {T : Finset V} (ht : Antichain T) (hc : T.card = 3) {x : V} (hx : x ∉ T) :
    (T.filter (IncRel x)).card ≤ 1 := by sorry
