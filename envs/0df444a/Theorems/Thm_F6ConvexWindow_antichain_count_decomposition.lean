-- Prove2me | Theorems.Thm_F6ConvexWindow_antichain_count_decomposition
-- name    : F6ConvexWindow.antichain_count_decomposition
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T09:35:45.917312+00:00
-- url     : https://prove2.me/theorems/d68d6624-275e-53a5-a9a8-704bce527aad
-- title:
--   F6 Convex Window: antichain count decomposition
-- statement:
--   Exhaustive decomposition into antichain sizes; no counts are supplied as assumptions.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L471-L475
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L471-L475

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.antichain_count_decomposition (k : ℕ) (hw : WidthLE (V := V) k) :
    totalAntichains (V := V) = ∑ j ∈ range (k + 1), Ak (V := V) j := by sorry
