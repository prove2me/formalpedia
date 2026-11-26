-- Prove2me | Theorems.Thm_CSeparatedNPComplete_hinge_form_snoc
-- name    : CSeparatedNPComplete.hinge_form_snoc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:48:27.7818+00:00
-- url     : https://prove2.me/theorems/3aa659e0-2250-4695-9c8a-e4777b3b7ff0
-- title:
--   CSeparated NPComplete: hinge form snoc
-- statement:
--   The CSeparated NPComplete construction uses the hinge form snoc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PartitionBasic.lean#L134-L143
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PartitionBasic.lean#L134-L143

module
public import Definitions.Def_CSeparatedNPComplete_PartitionDefs
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.hinge_form_snoc {n : Nat} (c : ℝ) (a : Vec n)
    (L : List (Gaussian n)) (g : Gaussian n) :
    hinge_form c a (L ++ [g]) = hinge_form c a L + hinge_to c a L g := by sorry
