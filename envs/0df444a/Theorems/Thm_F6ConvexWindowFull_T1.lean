-- Prove2me | Theorems.Thm_F6ConvexWindowFull_T1
-- name    : F6ConvexWindowFull.T1
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T10:13:28.393479+00:00
-- url     : https://prove2.me/theorems/72f0f261-f328-4db5-89ce-6f93b9bb5209
-- title:
--   F6 Convex Window Full: T1
-- statement:
--   T1: the unchanged parent result under exactly W3, CI2, and A3 > 0.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowFull.lean#L77-L79
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowFull.lean#L77-L79

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_DilworthTheorem
import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
set_option autoImplicit true
noncomputable section
open F6ConvexWindowFull
open F6ConvexWindow
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindowFull.T1 (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    (hpos : 0 < Ak (V := V) 3) : 2 * Ak (V := V) 3 + 1 ≤ Fintype.card V := by sorry
