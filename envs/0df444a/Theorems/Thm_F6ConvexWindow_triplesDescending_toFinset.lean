-- Prove2me | Theorems.Thm_F6ConvexWindow_triplesDescending_toFinset
-- name    : F6ConvexWindow.triplesDescending_toFinset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:40:36.493294+00:00
-- url     : https://prove2.me/theorems/170a3646-820b-5c3a-9e00-3aa371528af6
-- title:
--   F6 Convex Window: triples Descending to Finset
-- statement:
--   The F6 Convex Window construction uses the triples Descending to Finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L226-L235
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L226-L235

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.triplesDescending_toFinset (F : Finset (Finset V)) :
    (triplesDescending F).toFinset = F := by sorry
