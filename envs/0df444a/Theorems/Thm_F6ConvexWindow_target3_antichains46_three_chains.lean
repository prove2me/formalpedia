-- Prove2me | Theorems.Thm_F6ConvexWindow_target3_antichains46_three_chains
-- name    : F6ConvexWindow.target3_antichains46_three_chains
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:10:10.437477+00:00
-- url     : https://prove2.me/theorems/582863f9-6cd1-41b1-b626-41968554c1f8
-- title:
--   F6 Convex Window: target3 antichains46 three chains
-- statement:
--   Frozen target 3 conditional only on the explicitly displayed Dilworth decomposition.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L600-L606
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L600-L606

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.target3_antichains46_three_chains (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    (hpos : 0 < Ak (V := V) 3) (hn : Fintype.card V ≤ 14)
    (d : ChainDecomposition (V := V) 3) : totalAntichains (V := V) ≤ 46 := by sorry
