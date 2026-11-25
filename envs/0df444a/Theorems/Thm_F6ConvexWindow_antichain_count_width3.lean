-- Prove2me | Theorems.Thm_F6ConvexWindow_antichain_count_width3
-- name    : F6ConvexWindow.antichain_count_width3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:33:27.893947+00:00
-- url     : https://prove2.me/theorems/55e5ca3a-0d79-4bc7-b955-59bb085e5bcf
-- title:
--   F6 Convex Window: antichain count width3
-- statement:
--   The F6 Convex Window construction uses the antichain count width3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L477-L480
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L477-L480

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.antichain_count_width3 (hw : WidthLE (V := V) 3) :
    totalAntichains (V := V) = 1 + Fintype.card V + Ak (V := V) 2 + Ak (V := V) 3 := by sorry
