-- Prove2me | Theorems.Thm_F6ConvexWindow_mem_Inc
-- name    : F6ConvexWindow.mem_Inc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:30:58.687333+00:00
-- url     : https://prove2.me/theorems/f7cfd81d-d0c4-5a1e-8e43-69a322053c10
-- title:
--   F6 Convex Window: mem Inc
-- statement:
--   The F6 Convex Window construction uses the mem Inc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L40-L42
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L40-L42

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.mem_Inc {x z : V} : z ∈ Inc x ↔ IncRel x z := by sorry
