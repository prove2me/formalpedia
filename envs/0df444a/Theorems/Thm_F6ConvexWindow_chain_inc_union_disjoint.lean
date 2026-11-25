-- Prove2me | Theorems.Thm_F6ConvexWindow_chain_inc_union_disjoint
-- name    : F6ConvexWindow.chain_inc_union_disjoint
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T10:05:52.833161+00:00
-- url     : https://prove2.me/theorems/7bda7f1b-0141-4e09-80be-a8f83f5b8000
-- title:
--   F6 Convex Window: chain inc union disjoint
-- statement:
--   A chain contains no member of any of its own incomparability sets.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L416-L423
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L416-L423

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.chain_inc_union_disjoint {C : Finset V} (hc : Chain C) :
    Disjoint C (C.biUnion Inc) := by sorry
