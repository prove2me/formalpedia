-- Prove2me | Theorems.Thm_F6ConvexWindow_below_lt_above
-- name    : F6ConvexWindow.below_lt_above
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:31:56.539899+00:00
-- url     : https://prove2.me/theorems/2ac0a374-e32d-4061-a934-887966ddc373
-- title:
--   F6 Convex Window: below lt above
-- statement:
--   The two two-element subsets of a triple overlap (§7a).
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L212-L226
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L212-L226

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.below_lt_above {T : Finset V} (hc : T.card = 3) {l u : V}
    (hl : Below T l) (hu : Above T u) : l < u := by sorry
