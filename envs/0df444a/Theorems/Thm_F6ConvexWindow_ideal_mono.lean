-- Prove2me | Theorems.Thm_F6ConvexWindow_ideal_mono
-- name    : F6ConvexWindow.ideal_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:01:49.346861+00:00
-- url     : https://prove2.me/theorems/efdb0d7e-6e78-5585-80b1-2c498d49879b
-- title:
--   F6 Convex Window: ideal mono
-- statement:
--   The F6 Convex Window construction uses the ideal mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L64-L68
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L64-L68

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.ideal_mono {s t : Finset V} (h : s ⊆ ideal t) : ideal s ⊆ ideal t := by sorry
