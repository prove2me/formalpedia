-- Prove2me | Theorems.Thm_F6ConvexWindow_ordered_actual_triples
-- name    : F6ConvexWindow.ordered_actual_triples
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:44:59.679631+00:00
-- url     : https://prove2.me/theorems/f5754610-19fc-41bd-9e1d-75f3d752d8e7
-- title:
--   F6 Convex Window: ordered actual triples
-- statement:
--   §1: all actual triple antichains, strictly ordered by their generated ideals.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L263-L269
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L263-L269

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.ordered_actual_triples (hw : WidthLE (V := V) 3) (hci : CI2 (V := V)) :
    ∃ L : List (Finset V), L.toFinset = tripleFamily ∧
      L.Pairwise (fun S T => ideal S ⊂ ideal T) := by sorry
