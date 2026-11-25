-- Prove2me | Theorems.Thm_F6ConvexWindow_target4_antichains36_two_chains
-- name    : F6ConvexWindow.target4_antichains36_two_chains
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:11:01.388834+00:00
-- url     : https://prove2.me/theorems/61c290ac-d9d1-472d-b98a-f96e18b8445c
-- title:
--   F6 Convex Window: target4 antichains36 two chains
-- statement:
--   Frozen target 4 conditional only on the explicit two-chain instance of Dilworth.
--   Empty fibers cover width zero and one without a nonemptiness assumption.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L665-L688
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L665-L688

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.target4_antichains36_two_chains (hw : WidthLE (V := V) 2) (hci : CI2 (V := V))
    (hn : Fintype.card V ≤ 15) (d : ChainDecomposition (V := V) 2) :
    totalAntichains (V := V) ≤ 36 := by sorry
