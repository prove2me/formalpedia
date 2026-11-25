-- Prove2me | Theorems.Thm_F6ConvexWindow_w3_antichain_card_le
-- name    : F6ConvexWindow.w3_antichain_card_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T10:11:54.619461+00:00
-- url     : https://prove2.me/theorems/e0eb1dba-f5ad-5f30-93f1-3ada6bce4e58
-- title:
--   F6 Convex Window: w3 antichain card le
-- statement:
--   W3 in the frozen parent is exactly `WidthLE 3`.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowFull.lean#L28-L30
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowFull.lean#L28-L30

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_DilworthTheorem
import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.w3_antichain_card_le (hw : WidthLE (V := V) 3) (A : Finset V)
    (hA : DilworthTheorem.IsAntichain (A : Set V)) : A.card ≤ 3 := by sorry
