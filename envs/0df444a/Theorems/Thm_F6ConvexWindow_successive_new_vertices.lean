-- Prove2me | Theorems.Thm_F6ConvexWindow_successive_new_vertices
-- name    : F6ConvexWindow.successive_new_vertices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T11:06:45.681513+00:00
-- url     : https://prove2.me/theorems/85d51c08-a480-4ee9-91ad-8113c06f3df4
-- title:
--   F6 Convex Window: successive new vertices
-- statement:
--   §1: every successive triple introduces exactly two or three new vertices.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L486-L494
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L486-L494

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.successive_new_vertices (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    {G : Finset (Finset V)} (hg : ∀ R ∈ G, IsTriple R) {S T : Finset V}
    (hSG : S ∈ G) (hSmax : ∀ R ∈ G, (ideal R).card ≤ (ideal S).card)
    (ht : IsTriple T) (hST : ideal S ⊆ ideal T) (hTG : T ∉ G) :
    (T \ tripleUnion G).card = 2 ∨ (T \ tripleUnion G).card = 3 := by sorry
