-- Prove2me | Theorems.Thm_F6ConvexWindow_triple_comparison
-- name    : F6ConvexWindow.triple_comparison
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:32:25.761566+00:00
-- url     : https://prove2.me/theorems/4055d978-6908-5cef-9d26-9ec293bdddce
-- title:
--   F6 Convex Window: triple comparison
-- statement:
--   A maximum-size triple meets every outside point by a comparison (§7a).
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L116-L135
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L116-L135

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.triple_comparison (hw : WidthLE (V := V) 3) {T : Finset V}
    (ht : Antichain T) (hc : T.card = 3) {x : V} (hx : x ∉ T) :
    ∃ y ∈ T, x ≤ y ∨ y ≤ x := by sorry
