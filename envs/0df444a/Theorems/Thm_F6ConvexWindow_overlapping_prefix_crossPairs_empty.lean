-- Prove2me | Theorems.Thm_F6ConvexWindow_overlapping_prefix_crossPairs_empty
-- name    : F6ConvexWindow.overlapping_prefix_crossPairs_empty
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T10:21:20.48388+00:00
-- url     : https://prove2.me/theorems/87a0b981-23f4-4d59-b657-e18a2c756fa5
-- title:
--   F6 Convex Window: overlapping prefix cross Pairs empty
-- statement:
--   §3, one-vertex overlap: there are no old-only/new-only incomparable pairs.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L429-L445
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L429-L445

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.overlapping_prefix_crossPairs_empty (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    {G : Finset (Finset V)} (hg : ∀ R ∈ G, IsTriple R) {S T : Finset V}
    (hSG : S ∈ G) (hSmax : ∀ R ∈ G, (ideal R).card ≤ (ideal S).card)
    (ht : IsTriple T) (hST : ideal S ⊆ ideal T) (hover : (S ∩ T).Nonempty) :
    crossPairs (tripleUnion G \ T) (T \ tripleUnion G) = ∅ := by sorry
