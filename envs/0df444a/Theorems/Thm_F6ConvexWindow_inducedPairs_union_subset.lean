-- Prove2me | Theorems.Thm_F6ConvexWindow_inducedPairs_union_subset
-- name    : F6ConvexWindow.inducedPairs_union_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:17:58.155839+00:00
-- url     : https://prove2.me/theorems/3a30e84e-ee5f-4d59-a558-6db053ea076b
-- title:
--   F6 Convex Window: induced Pairs union subset
-- statement:
--   Finite-set adapter for the three classes of pairs when a set is appended.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L145-L178
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L145-L178

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.inducedPairs_union_subset (U W : Finset V) :
    inducedPairs (U ∪ W) ⊆ inducedPairs U ∪ inducedPairs W ∪ crossPairs (U \ W) (W \ U) := by sorry
