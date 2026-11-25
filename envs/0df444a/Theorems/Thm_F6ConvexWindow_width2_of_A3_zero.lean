-- Prove2me | Theorems.Thm_F6ConvexWindow_width2_of_A3_zero
-- name    : F6ConvexWindow.width2_of_A3_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T10:15:57.04824+00:00
-- url     : https://prove2.me/theorems/1ae1e50d-233c-589f-b3ce-be31eb7a3196
-- title:
--   F6 Convex Window: width2 of A3 zero
-- statement:
--   A no-triple case under width three has width at most two.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L84-L93
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L84-L93

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.width2_of_A3_zero (hw : WidthLE (V := V) 3) (hzero : Ak (V := V) 3 = 0) :
    WidthLE (V := V) 2 := by sorry
