-- Prove2me | Theorems.Thm_F6ConvexWindow_overlapping_triples_comparable
-- name    : F6ConvexWindow.overlapping_triples_comparable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T10:15:43.215899+00:00
-- url     : https://prove2.me/theorems/f8a631f3-11cb-57c3-af66-fc926ee96c29
-- title:
--   F6 Convex Window: overlapping triples comparable
-- statement:
--   §3, nonempty transition: every old-only/new-only pair is comparable.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L72-L81
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L72-L81

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.overlapping_triples_comparable (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    {S T : Finset V} (hs : IsTriple S) (ht : IsTriple T)
    (hST : ideal S ⊆ ideal T) (hover : (S ∩ T).Nonempty)
    {x y : V} (hxS : x ∈ S) (hxT : x ∉ T) (hyT : y ∈ T) (hyS : y ∉ S) : x < y := by sorry
