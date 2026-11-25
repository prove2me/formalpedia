-- Prove2me | Theorems.Thm_F6ConvexWindow_adjacent_common_bound
-- name    : F6ConvexWindow.adjacent_common_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:02:34.127102+00:00
-- url     : https://prove2.me/theorems/16d270b5-dfed-51d4-b985-3fed35f78402
-- title:
--   F6 Convex Window: adjacent common bound
-- statement:
--   The adjacent common-incomparability bound is an immediate CI2 projection.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L102-L103
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L102-L103

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.adjacent_common_bound (hci : CI2 (V := V)) {x y : V} (hxy : x < y) :
    (Inc x ∩ Inc y).card ≤ 2 := by sorry
