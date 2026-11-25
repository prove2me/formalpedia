-- Prove2me | Theorems.Thm_F6ConvexWindow_triple_union_lower_bound
-- name    : F6ConvexWindow.triple_union_lower_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T10:04:42.506713+00:00
-- url     : https://prove2.me/theorems/1656a95d-26a4-478c-bd23-2eb17401953d
-- title:
--   F6 Convex Window: triple union lower bound
-- statement:
--   §7d counting: the first triple contributes three, each later triple at least two.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L307-L346
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L307-L346

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.triple_union_lower_bound (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    (F : Finset (Finset V)) (hf : ∀ T ∈ F, Antichain T ∧ T.card = 3)
    (hn : F.Nonempty) : 2 * F.card + 1 ≤ (F.biUnion id).card := by sorry
