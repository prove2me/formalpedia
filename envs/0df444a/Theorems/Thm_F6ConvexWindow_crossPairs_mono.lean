-- Prove2me | Theorems.Thm_F6ConvexWindow_crossPairs_mono
-- name    : F6ConvexWindow.crossPairs_mono
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T10:16:52.664942+00:00
-- url     : https://prove2.me/theorems/a55bcf35-5589-459b-8f8a-14ded47ee993
-- title:
--   F6 Convex Window: cross Pairs mono
-- statement:
--   The F6 Convex Window construction uses the cross Pairs mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L135-L142
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L135-L142

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.crossPairs_mono {U U' W W' : Finset V} (hU : U ⊆ U') (hW : W ⊆ W') :
    crossPairs U W ⊆ crossPairs U' W' := by sorry
