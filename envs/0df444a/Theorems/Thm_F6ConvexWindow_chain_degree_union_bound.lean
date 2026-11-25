-- Prove2me | Theorems.Thm_F6ConvexWindow_chain_degree_union_bound
-- name    : F6ConvexWindow.chain_degree_union_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:05:41.283157+00:00
-- url     : https://prove2.me/theorems/78268dc3-bbdb-4655-a251-fdda8fa70616
-- title:
--   F6 Convex Window: chain degree union bound
-- statement:
--   The exact union recurrence plus CI2 bounds every adjacent overlap by two.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L383-L413
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L383-L413

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.chain_degree_union_bound (hci : CI2 (V := V)) (C : Finset V)
    (hc : Chain C) (hn : C.Nonempty) :
    (∑ x ∈ C, (Inc x).card) + 2 ≤ (C.biUnion Inc).card + 2 * C.card := by sorry
