-- Prove2me | Theorems.Thm_F6ConvexWindow_totalAntichains_le_46_of_six_triples
-- name    : F6ConvexWindow.totalAntichains_le_46_of_six_triples
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:23:21.880231+00:00
-- url     : https://prove2.me/theorems/21a258c7-dc29-4978-bfab-f5df324b3670
-- title:
--   F6 Convex Window: total Antichains le 46 of six triples
-- statement:
--   §5, equation (7): the stronger bound when n=15 and there are at least six triples.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L627-L653
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L627-L653

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.totalAntichains_le_46_of_six_triples (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    (hn : Fintype.card V = 15) (ht : 6 ≤ Ak (V := V) 3) : totalAntichains (V := V) ≤ 46 := by sorry
