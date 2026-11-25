-- Prove2me | Theorems.Thm_F6ConvexWindow_triple_ideals_nested
-- name    : F6ConvexWindow.triple_ideals_nested
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:03:31.501302+00:00
-- url     : https://prove2.me/theorems/dc4e297a-0b66-5c31-9259-ec416a3f194a
-- title:
--   F6 Convex Window: triple ideals nested
-- statement:
--   §7b: all generated ideals of triple antichains are nested.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L248-L279
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L248-L279

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.triple_ideals_nested (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    {S T : Finset V} (hs : Antichain S) (ht : Antichain T)
    (hsc : S.card = 3) (htc : T.card = 3) :
    ideal S ⊆ ideal T ∨ ideal T ⊆ ideal S := by sorry
