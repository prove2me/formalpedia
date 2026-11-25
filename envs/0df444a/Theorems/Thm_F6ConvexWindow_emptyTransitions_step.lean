-- Prove2me | Theorems.Thm_F6ConvexWindow_emptyTransitions_step
-- name    : F6ConvexWindow.emptyTransitions_step
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T11:12:02.964802+00:00
-- url     : https://prove2.me/theorems/6357e1cc-17f5-405b-a606-1d2ea4a6c17b
-- title:
--   F6 Convex Window: empty Transitions step
-- statement:
--   The recursive counter is the count of disjoint consecutive triples in the
--   same ideal order: at a noninitial step its test is exactly the predecessor test.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L564-L587
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindowN15.lean#L564-L587

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.emptyTransitions_step (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    (F : Finset (Finset V)) (hf : ∀ T ∈ F, IsTriple T) (hn : F.Nonempty)
    (hGn : (F.erase (lastTriple F hn)).Nonempty) :
    emptyTransitions F = emptyTransitions (F.erase (lastTriple F hn)) +
      if Disjoint (lastTriple (F.erase (lastTriple F hn)) hGn) (lastTriple F hn) then 1 else 0 := by sorry
