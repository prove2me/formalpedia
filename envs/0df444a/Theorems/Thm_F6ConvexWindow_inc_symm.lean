-- Prove2me | Theorems.Thm_F6ConvexWindow_inc_symm
-- name    : F6ConvexWindow.inc_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:34:52.812194+00:00
-- url     : https://prove2.me/theorems/964f4a54-8dc7-5df7-8d67-d1aff1765444
-- title:
--   F6 Convex Window: inc symm
-- statement:
--   The F6 Convex Window construction uses the inc symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L54-L54
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L54-L54

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.inc_symm {x y : V} (h : IncRel x y) : IncRel y x := by sorry
