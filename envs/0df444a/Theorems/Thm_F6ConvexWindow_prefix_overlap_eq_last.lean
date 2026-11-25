-- Prove2me | Theorems.Thm_F6ConvexWindow_prefix_overlap_eq_last
-- name    : F6ConvexWindow.prefix_overlap_eq_last
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T09:33:35.561978+00:00
-- url     : https://prove2.me/theorems/9877e648-8eb6-5d3c-9409-0115a0363dcc
-- title:
--   F6 Convex Window: prefix overlap eq last
-- statement:
--   The previous triple contains every vertex of the new triple already in the prefix.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L284-L299
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L284-L299

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.prefix_overlap_eq_last (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    {G : Finset (Finset V)} (hg : ∀ R ∈ G, IsTriple R) {S T : Finset V}
    (hSG : S ∈ G) (hSmax : ∀ R ∈ G, (ideal R).card ≤ (ideal S).card)
    (ht : IsTriple T) (hST : ideal S ⊆ ideal T) :
    T ∩ tripleUnion G = T ∩ S := by sorry
