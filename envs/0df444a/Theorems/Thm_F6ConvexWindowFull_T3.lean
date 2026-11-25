-- Prove2me | Theorems.Thm_F6ConvexWindowFull_T3
-- name    : F6ConvexWindowFull.T3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:13:43.050311+00:00
-- url     : https://prove2.me/theorems/aed13c1f-cd32-474f-aee8-a900baaea90b
-- title:
--   F6 Convex Window Full: T3
-- statement:
--   T3: the frozen bound for at most fourteen vertices.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowFull.lean#L88-L92
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowFull.lean#L88-L92

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_DilworthTheorem
import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
set_option autoImplicit true
noncomputable section
open F6ConvexWindowFull
open F6ConvexWindow
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindowFull.T3 (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    (hpos : 0 < Ak (V := V) 3) (hn : Fintype.card V ≤ 14) :
    totalAntichains (V := V) ≤ 46 := by sorry
