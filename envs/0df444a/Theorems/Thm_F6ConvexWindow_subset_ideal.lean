-- Prove2me | Theorems.Thm_F6ConvexWindow_subset_ideal
-- name    : F6ConvexWindow.subset_ideal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:31:12.024011+00:00
-- url     : https://prove2.me/theorems/ee75f24f-2c33-5ed7-8e78-55aa1c43e7d4
-- title:
--   F6 Convex Window: subset ideal
-- statement:
--   The F6 Convex Window construction uses the subset ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L60-L62
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L60-L62

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.subset_ideal (s : Finset V) : s ⊆ ideal s := by sorry
