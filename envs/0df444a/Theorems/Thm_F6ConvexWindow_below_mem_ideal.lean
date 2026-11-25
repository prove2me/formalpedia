-- Prove2me | Theorems.Thm_F6ConvexWindow_below_mem_ideal
-- name    : F6ConvexWindow.below_mem_ideal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:32:48.573977+00:00
-- url     : https://prove2.me/theorems/33d098ea-49e2-58b2-a845-7bfc9eb0c360
-- title:
--   F6 Convex Window: below mem ideal
-- statement:
--   The F6 Convex Window construction uses the below mem ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L228-L234
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L228-L234

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.below_mem_ideal {T : Finset V} {x : V} (h : Below T x) : x ∈ ideal T := by sorry
