-- Prove2me | Theorems.Thm_F6ConvexWindow_pairCount_union_le
-- name    : F6ConvexWindow.pairCount_union_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:38:36.801727+00:00
-- url     : https://prove2.me/theorems/9ca3c66b-3f11-5f99-8b8b-7544131f9470
-- title:
--   F6 Convex Window: pair Count union le
-- statement:
--   The F6 Convex Window construction uses the pair Count union le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L180-L185
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L180-L185

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.pairCount_union_le (U W : Finset V) :
    pairCount (U ∪ W) ≤ pairCount U + pairCount W + (crossPairs (U \ W) (W \ U)).card := by sorry
