-- Prove2me | Theorems.Thm_F6ConvexWindow_triple_union_counts
-- name    : F6ConvexWindow.triple_union_counts
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T10:21:53.670052+00:00
-- url     : https://prove2.me/theorems/bed88c85-31db-52e8-a252-843909c16054
-- title:
--   F6 Convex Window: triple union counts
-- statement:
--   §1–§3, equations (1) and (2), by induction over the ideal-ordered prefixes.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L512-L560
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L512-L560

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.triple_union_counts (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    (F : Finset (Finset V)) (hf : ∀ T ∈ F, IsTriple T) (hn : F.Nonempty) :
    (tripleUnion F).card = 2 * F.card + 1 + emptyTransitions F ∧
    pairCount (tripleUnion F) ≤ 3 * F.card + 3 * emptyTransitions F := by sorry
