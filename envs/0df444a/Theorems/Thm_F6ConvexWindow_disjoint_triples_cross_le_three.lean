-- Prove2me | Theorems.Thm_F6ConvexWindow_disjoint_triples_cross_le_three
-- name    : F6ConvexWindow.disjoint_triples_cross_le_three
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T10:19:02.99368+00:00
-- url     : https://prove2.me/theorems/b869a6f7-8abb-4ed1-8248-42e35c5a00fc
-- title:
--   F6 Convex Window: disjoint triples cross le three
-- statement:
--   The F6 Convex Window construction uses the disjoint triples cross le three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L200-L205
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L200-L205

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.disjoint_triples_cross_le_three (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    {S T : Finset V} (hs : IsTriple S) (ht : IsTriple T) (hd : Disjoint S T) :
    (crossPairs S T).card ≤ 3 := by sorry
