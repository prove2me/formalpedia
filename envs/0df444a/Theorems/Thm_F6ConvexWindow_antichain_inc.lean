-- Prove2me | Theorems.Thm_F6ConvexWindow_antichain_inc
-- name    : F6ConvexWindow.antichain_inc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:31:18.711405+00:00
-- url     : https://prove2.me/theorems/76bef37c-8cd9-5684-bd10-8d6322bd1b51
-- title:
--   F6 Convex Window: antichain inc
-- statement:
--   The F6 Convex Window construction uses the antichain inc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L56-L58
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L56-L58

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.antichain_inc {s : Finset V} (h : Antichain s)
    {x y : V} (hx : x ∈ s) (hy : y ∈ s) (hne : x ≠ y) : IncRel x y := by sorry
