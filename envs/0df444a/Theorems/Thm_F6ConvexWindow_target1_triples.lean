-- Prove2me | Theorems.Thm_F6ConvexWindow_target1_triples
-- name    : F6ConvexWindow.target1_triples
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T09:34:22.499617+00:00
-- url     : https://prove2.me/theorems/1b183ae4-aad5-426d-8c66-222d453a8916
-- title:
--   F6 Convex Window: target1 triples
-- statement:
--   Frozen target 1, with the actual number of three-element antichains.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L349-L357
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L349-L357

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.target1_triples (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    (hpos : 0 < Ak (V := V) 3) : 2 * Ak (V := V) 3 + 1 ≤ Fintype.card V := by sorry
