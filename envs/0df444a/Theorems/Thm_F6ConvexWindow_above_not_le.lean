-- Prove2me | Theorems.Thm_F6ConvexWindow_above_not_le
-- name    : F6ConvexWindow.above_not_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:32:59.143542+00:00
-- url     : https://prove2.me/theorems/317554c1-6c4d-552b-a2bd-2eb8dad64031
-- title:
--   F6 Convex Window: above not le
-- statement:
--   The F6 Convex Window construction uses the above not le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L236-L245
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L236-L245

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.above_not_le {T : Finset V} (ht : Antichain T) {x t : V}
    (hx : Above T x) (htT : t ∈ T) : ¬ x ≤ t := by sorry
