-- Prove2me | Theorems.Thm_F6ConvexWindow_triple_intersection_le_one
-- name    : F6ConvexWindow.triple_intersection_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:34:10.703228+00:00
-- url     : https://prove2.me/theorems/6ace4be1-7175-536d-9d9d-a6ef672c5407
-- title:
--   F6 Convex Window: triple intersection le one
-- statement:
--   §7c: distinct triple antichains share at most one element.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L282-L294
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L282-L294

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.triple_intersection_le_one (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    {S T : Finset V} (hs : Antichain S) (ht : Antichain T)
    (hsc : S.card = 3) (htc : T.card = 3) (hne : S ≠ T) : (S ∩ T).card ≤ 1 := by sorry
