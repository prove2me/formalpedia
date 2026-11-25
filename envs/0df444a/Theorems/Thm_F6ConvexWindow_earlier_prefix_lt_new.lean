-- Prove2me | Theorems.Thm_F6ConvexWindow_earlier_prefix_lt_new
-- name    : F6ConvexWindow.earlier_prefix_lt_new
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:40:39.270247+00:00
-- url     : https://prove2.me/theorems/c4afb733-0018-5de1-a325-00e6ae82f999
-- title:
--   F6 Convex Window: earlier prefix lt new
-- statement:
--   A vertex in a still-earlier triple cannot create an extra new cross edge.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L302-L312
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L302-L312

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.earlier_prefix_lt_new (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    {G : Finset (Finset V)} (hg : ∀ R ∈ G, IsTriple R) {S T : Finset V}
    (hSG : S ∈ G) (hSmax : ∀ R ∈ G, (ideal R).card ≤ (ideal S).card)
    (ht : IsTriple T) (hST : ideal S ⊆ ideal T) {x y : V}
    (hx : x ∈ tripleUnion G) (hxS : x ∉ S) (hyT : y ∈ T) (hyS : y ∉ S) : x < y := by sorry
