-- Prove2me | Theorems.Thm_F6ConvexWindow_earlier_exclusive_below
-- name    : F6ConvexWindow.earlier_exclusive_below
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:33:20.367976+00:00
-- url     : https://prove2.me/theorems/d3d24a43-4cce-5816-b9bb-fb4470800a2d
-- title:
--   F6 Convex Window: earlier exclusive below
-- statement:
--   §2: an earlier-exclusive point is Below the later triple.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L32-L38
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L32-L38

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.earlier_exclusive_below (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    {S T : Finset V} (ht : IsTriple T) (hST : ideal S ⊆ ideal T)
    {x : V} (hxS : x ∈ S) (hxT : x ∉ T) : Below T x := by sorry
