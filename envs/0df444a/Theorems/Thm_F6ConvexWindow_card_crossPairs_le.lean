-- Prove2me | Theorems.Thm_F6ConvexWindow_card_crossPairs_le
-- name    : F6ConvexWindow.card_crossPairs_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T09:38:14.064422+00:00
-- url     : https://prove2.me/theorems/c747467b-1cee-521d-8eae-7bbfdf914005
-- title:
--   F6 Convex Window: card cross Pairs le
-- statement:
--   The F6 Convex Window construction uses the card cross Pairs le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L130-L133
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L130-L133

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.card_crossPairs_le (U W : Finset V) : (crossPairs U W).card ≤ crossCount U W := by sorry
