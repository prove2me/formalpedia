-- Prove2me | Theorems.Thm_F6ConvexWindow_target2_pairs_three_chains
-- name    : F6ConvexWindow.target2_pairs_three_chains
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:37:28.213732+00:00
-- url     : https://prove2.me/theorems/dac8a892-9f5b-5ea6-889a-37d40515ff26
-- title:
--   F6 Convex Window: target2 pairs three chains
-- statement:
--   Frozen target 2 conditional only on the explicitly displayed Dilworth decomposition.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L584-L597
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L584-L597

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.target2_pairs_three_chains (_hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    (hpos : 0 < Ak (V := V) 3) (d : ChainDecomposition (V := V) 3) :
    Ak (V := V) 2 + 3 ≤ 2 * Fintype.card V := by sorry
