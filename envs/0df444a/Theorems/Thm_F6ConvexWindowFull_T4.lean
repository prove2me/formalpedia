-- Prove2me | Theorems.Thm_F6ConvexWindowFull_T4
-- name    : F6ConvexWindowFull.T4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:13:31.360521+00:00
-- url     : https://prove2.me/theorems/3a1f6d41-be10-53e1-8276-b1f8d80e0ccf
-- title:
--   F6 Convex Window Full: T4
-- statement:
--   T4: width at most two, including empty posets and empty chain fibers.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowFull.lean#L95-L98
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowFull.lean#L95-L98

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_DilworthTheorem
import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
set_option autoImplicit true
noncomputable section
open F6ConvexWindowFull
open F6ConvexWindow
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindowFull.T4 (hw : WidthLE (V := V) 2) (hci : CI2 (V := V))
    (hn : Fintype.card V ≤ 15) : totalAntichains (V := V) ≤ 36 := by sorry
