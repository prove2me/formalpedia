-- Prove2me | Theorems.Thm_F6ConvexWindow_prefix_pairCount_step
-- name    : F6ConvexWindow.prefix_pairCount_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:21:31.939906+00:00
-- url     : https://prove2.me/theorems/d8d5b2f3-60a7-5874-9796-3c1da118358f
-- title:
--   F6 Convex Window: prefix pair Count step
-- statement:
--   §3: a new triple adds at most three internal pairs and, only for an empty
--   transition, at most three cross pairs.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L449-L473
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L449-L473

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.prefix_pairCount_step (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    {G : Finset (Finset V)} (hg : ∀ R ∈ G, IsTriple R) {S T : Finset V}
    (hSG : S ∈ G) (hSmax : ∀ R ∈ G, (ideal R).card ≤ (ideal S).card)
    (ht : IsTriple T) (hST : ideal S ⊆ ideal T) :
    pairCount (tripleUnion G ∪ T) ≤ pairCount (tripleUnion G) + 3 +
      if Disjoint (tripleUnion G) T then 3 else 0 := by sorry
