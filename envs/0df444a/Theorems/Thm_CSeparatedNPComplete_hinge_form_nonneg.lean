-- Prove2me | Theorems.Thm_CSeparatedNPComplete_hinge_form_nonneg
-- name    : CSeparatedNPComplete.hinge_form_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:48:10.792796+00:00
-- url     : https://prove2.me/theorems/0392ad56-8f8a-4732-8749-bd68d2e4d539
-- title:
--   CSeparated NPComplete: hinge form nonneg
-- statement:
--   The CSeparated NPComplete construction uses the hinge form nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PartitionBasic.lean#L102-L106
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PartitionBasic.lean#L102-L106

module
public import Definitions.Def_CSeparatedNPComplete_PartitionDefs
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.hinge_form_nonneg {n : Nat} (c : ℝ) (a : Vec n) (L : List (Gaussian n)) :
    0 ≤ hinge_form c a L := by sorry
