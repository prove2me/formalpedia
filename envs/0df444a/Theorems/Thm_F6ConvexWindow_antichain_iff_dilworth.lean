-- Prove2me | Theorems.Thm_F6ConvexWindow_antichain_iff_dilworth
-- name    : F6ConvexWindow.antichain_iff_dilworth
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T09:38:04.050256+00:00
-- url     : https://prove2.me/theorems/9448e7b6-1c11-40e8-9bfb-4bd3d7db09b5
-- title:
--   F6 Convex Window: antichain iff dilworth
-- statement:
--   The parent and the reference express the same antichain predicate.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowFull.lean#L18-L25
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowFull.lean#L18-L25

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_DilworthTheorem
import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.antichain_iff_dilworth (A : Finset V) :
    Antichain A ↔ DilworthTheorem.IsAntichain (A : Set V) := by sorry
