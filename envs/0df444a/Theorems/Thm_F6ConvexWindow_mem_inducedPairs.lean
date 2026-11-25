-- Prove2me | Theorems.Thm_F6ConvexWindow_mem_inducedPairs
-- name    : F6ConvexWindow.mem_inducedPairs
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T09:32:22.686491+00:00
-- url     : https://prove2.me/theorems/8fc3d751-3188-4de3-b4ea-016cf1feb0b5
-- title:
--   F6 Convex Window: mem induced Pairs
-- statement:
--   The F6 Convex Window construction uses the mem induced Pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L99-L101
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L99-L101

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.mem_inducedPairs {U P : Finset V} :
    P ∈ inducedPairs U ↔ P ⊆ U ∧ P.card = 2 ∧ Antichain P := by sorry
