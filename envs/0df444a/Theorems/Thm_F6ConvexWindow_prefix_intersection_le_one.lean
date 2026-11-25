-- Prove2me | Theorems.Thm_F6ConvexWindow_prefix_intersection_le_one
-- name    : F6ConvexWindow.prefix_intersection_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:41:08.294553+00:00
-- url     : https://prove2.me/theorems/2ba44852-425d-41f2-a070-805d87654f0f
-- title:
--   F6 Convex Window: prefix intersection le one
-- statement:
--   No-reentry and intersection at most one control the new vertices at each step.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L476-L483
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L476-L483

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.prefix_intersection_le_one (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    {G : Finset (Finset V)} (hg : ∀ R ∈ G, IsTriple R) {S T : Finset V}
    (hSG : S ∈ G) (hSmax : ∀ R ∈ G, (ideal R).card ≤ (ideal S).card)
    (ht : IsTriple T) (hST : ideal S ⊆ ideal T) (hTG : T ∉ G) :
    (tripleUnion G ∩ T).card ≤ 1 := by sorry
