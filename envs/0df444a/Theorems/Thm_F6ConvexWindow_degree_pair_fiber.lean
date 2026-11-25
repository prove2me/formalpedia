-- Prove2me | Theorems.Thm_F6ConvexWindow_degree_pair_fiber
-- name    : F6ConvexWindow.degree_pair_fiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:36:19.982844+00:00
-- url     : https://prove2.me/theorems/1e6c9306-774a-4774-808f-206212b114f9
-- title:
--   F6 Convex Window: degree pair fiber
-- statement:
--   Bijection between neighbors of a vertex and two-element antichains containing it.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L500-L522
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L500-L522

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.degree_pair_fiber (x : V) : (Inc x).card =
    (((antichains (V := V)).filter (fun T => T.card = 2)).filter (fun T => x ∈ T)).card := by sorry
