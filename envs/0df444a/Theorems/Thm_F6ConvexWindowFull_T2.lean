-- Prove2me | Theorems.Thm_F6ConvexWindowFull_T2
-- name    : F6ConvexWindowFull.T2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:17:53.920281+00:00
-- url     : https://prove2.me/theorems/cb4ad0a7-017c-4660-88bb-5c8294094cbe
-- title:
--   F6 Convex Window Full: T2
-- statement:
--   T2: no explicit three-chain decomposition is an input.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowFull.lean#L82-L85
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowFull.lean#L82-L85

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_DilworthTheorem
import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
set_option autoImplicit true
noncomputable section
open F6ConvexWindowFull
open F6ConvexWindow
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindowFull.T2 (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    (hpos : 0 < Ak (V := V) 3) : Ak (V := V) 2 + 3 ≤ 2 * Fintype.card V := by sorry
