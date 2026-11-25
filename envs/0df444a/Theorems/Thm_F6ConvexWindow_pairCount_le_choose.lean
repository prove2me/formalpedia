-- Prove2me | Theorems.Thm_F6ConvexWindow_pairCount_le_choose
-- name    : F6ConvexWindow.pairCount_le_choose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:16:42.518217+00:00
-- url     : https://prove2.me/theorems/1289a83e-24db-492a-87dd-b6d27802417b
-- title:
--   F6 Convex Window: pair Count le choose
-- statement:
--   The F6 Convex Window construction uses the pair Count le choose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L112-L113
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L112-L113

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.pairCount_le_choose (U : Finset V) : pairCount U ≤ U.card.choose 2 := by sorry
