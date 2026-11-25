-- Prove2me | Theorems.Thm_F6ConvexWindow_chain_adjacent_overlap
-- name    : F6ConvexWindow.chain_adjacent_overlap
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T10:05:36.286824+00:00
-- url     : https://prove2.me/theorems/ce17cb2f-d3fc-4b03-8c0c-e75b8b1aa7e7
-- title:
--   F6 Convex Window: chain adjacent overlap
-- statement:
--   Exact adjacent-overlap identity underlying the interval double count (§8).
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L369-L380
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L369-L380

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.chain_adjacent_overlap {C : Finset V} {x y : V}
    (hx : x ∈ C) (hmax : ∀ z ∈ C, z ≤ x) (hxy : x ≤ y) :
    (C.biUnion Inc) ∩ Inc y = Inc x ∩ Inc y := by sorry
