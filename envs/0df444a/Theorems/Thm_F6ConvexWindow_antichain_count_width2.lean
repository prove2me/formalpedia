-- Prove2me | Theorems.Thm_F6ConvexWindow_antichain_count_width2
-- name    : F6ConvexWindow.antichain_count_width2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:06:51.73133+00:00
-- url     : https://prove2.me/theorems/59efabc4-4e5a-464d-a70e-ff4799b90d30
-- title:
--   F6 Convex Window: antichain count width2
-- statement:
--   The F6 Convex Window construction uses the antichain count width2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L482-L485
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L482-L485

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.antichain_count_width2 (hw : WidthLE (V := V) 2) :
    totalAntichains (V := V) = 1 + Fintype.card V + Ak (V := V) 2 := by sorry
