-- Prove2me | Theorems.Thm_F6ConvexWindow_all_pairs_le_union_outsiders
-- name    : F6ConvexWindow.all_pairs_le_union_outsiders
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T10:22:07.731906+00:00
-- url     : https://prove2.me/theorems/192f6ec6-f4b1-581f-8db1-825462db81e2
-- title:
--   F6 Convex Window: all pairs le union outsiders
-- statement:
--   §5: partition the actual incomparable pairs into union, cross, and outsider pairs.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L590-L610
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L590-L610

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.all_pairs_le_union_outsiders (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    (F : Finset (Finset V)) (hf : ∀ T ∈ F, IsTriple T) :
    Ak (V := V) 2 ≤ pairCount (tripleUnion F) +
      2 * (univ \ tripleUnion F).card + (univ \ tripleUnion F).card.choose 2 := by sorry
