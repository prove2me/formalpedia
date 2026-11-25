-- Prove2me | Theorems.Thm_F6ConvexWindow_Ak_one
-- name    : F6ConvexWindow.Ak_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:35:51.619344+00:00
-- url     : https://prove2.me/theorems/0afe5d56-585b-4d88-912a-d4957260dbda
-- title:
--   F6 Convex Window: Ak one
-- statement:
--   §6: singleton antichains are counted exactly once per vertex.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L450-L468
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L450-L468

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.Ak_one : Ak (V := V) 1 = Fintype.card V := by sorry
