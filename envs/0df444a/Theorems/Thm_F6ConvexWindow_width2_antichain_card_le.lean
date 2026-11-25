-- Prove2me | Theorems.Thm_F6ConvexWindow_width2_antichain_card_le
-- name    : F6ConvexWindow.width2_antichain_card_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T10:12:42.396082+00:00
-- url     : https://prove2.me/theorems/aef5644e-73bd-44bc-8c8a-a6097132b997
-- title:
--   F6 Convex Window: width2 antichain card le
-- statement:
--   The width-two hypothesis supplies the reference's antichain bound.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowFull.lean#L33-L35
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowFull.lean#L33-L35

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_DilworthTheorem
import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.width2_antichain_card_le (hw : WidthLE (V := V) 2) (A : Finset V)
    (hA : DilworthTheorem.IsAntichain (A : Set V)) : A.card ≤ 2 := by sorry
