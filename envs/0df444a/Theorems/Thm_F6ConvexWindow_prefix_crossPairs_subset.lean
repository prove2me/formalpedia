-- Prove2me | Theorems.Thm_F6ConvexWindow_prefix_crossPairs_subset
-- name    : F6ConvexWindow.prefix_crossPairs_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:20:45.246378+00:00
-- url     : https://prove2.me/theorems/8e49b121-101f-41b3-bd76-c577526e6144
-- title:
--   F6 Convex Window: prefix cross Pairs subset
-- statement:
--   Localization of every new cross pair to the immediately preceding triple.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L410-L426
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L410-L426

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.prefix_crossPairs_subset (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    {G : Finset (Finset V)} (hg : ∀ R ∈ G, IsTriple R) {S T : Finset V}
    (hSG : S ∈ G) (hSmax : ∀ R ∈ G, (ideal R).card ≤ (ideal S).card)
    (ht : IsTriple T) (hST : ideal S ⊆ ideal T) :
    crossPairs (tripleUnion G \ T) (T \ tripleUnion G) ⊆ crossPairs S T := by sorry
