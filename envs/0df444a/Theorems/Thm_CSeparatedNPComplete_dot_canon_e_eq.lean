-- Prove2me | Theorems.Thm_CSeparatedNPComplete_dot_canon_e_eq
-- name    : CSeparatedNPComplete.dot_canon_e_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:47:43.346162+00:00
-- url     : https://prove2.me/theorems/5ab4be50-9029-4e8b-9474-a7acd1cc1ea2
-- title:
--   CSeparated NPComplete: dot canon e eq
-- statement:
--   The CSeparated NPComplete construction uses the dot canon e eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PartitionBasic.lean#L40-L44
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PartitionBasic.lean#L40-L44

module
public import Definitions.Def_CSeparatedNPComplete_PartitionDefs
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.dot_canon_e_eq {n : Nat} (a : Vec n) (i : Fin n) :
    dot a (canon_e i.val) = a i := by sorry
