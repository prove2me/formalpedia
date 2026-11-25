-- Prove2me | Theorems.Thm_F6ConvexWindow_card_tripleFamily
-- name    : F6ConvexWindow.card_tripleFamily
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:32:04.426333+00:00
-- url     : https://prove2.me/theorems/e03e4704-bde1-5dfa-84f2-e9ffe4ef09cd
-- title:
--   F6 Convex Window: card triple Family
-- statement:
--   The F6 Convex Window construction uses the card triple Family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L24-L24
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L24-L24

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.card_tripleFamily : (tripleFamily (V := V)).card = Ak (V := V) 3 := by sorry

attribute [defeq] F6ConvexWindow.card_tripleFamily
