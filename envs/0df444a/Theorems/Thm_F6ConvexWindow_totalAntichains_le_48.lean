-- Prove2me | Theorems.Thm_F6ConvexWindow_totalAntichains_le_48
-- name    : F6ConvexWindow.totalAntichains_le_48
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T09:40:40.919362+00:00
-- url     : https://prove2.me/theorems/4c0f31c5-7355-5053-85ad-2f4c5aa868d5
-- title:
--   F6 Convex Window: total Antichains le 48
-- statement:
--   The frozen N15 theorem, under the unchanged finite-poset definitions.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L656-L668
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L656-L668

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.totalAntichains_le_48 (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    (hn : Fintype.card V ≤ 15) : totalAntichains (V := V) ≤ 48 := by sorry
