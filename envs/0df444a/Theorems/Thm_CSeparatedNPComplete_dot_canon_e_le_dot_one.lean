-- Prove2me | Theorems.Thm_CSeparatedNPComplete_dot_canon_e_le_dot_one
-- name    : CSeparatedNPComplete.dot_canon_e_le_dot_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:47:44.622806+00:00
-- url     : https://prove2.me/theorems/2d20df51-a86e-59c6-8253-9055c6371c75
-- title:
--   CSeparated NPComplete: dot canon e le dot one
-- statement:
--   The CSeparated NPComplete construction uses the dot canon e le dot one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PartitionBasic.lean#L53-L58
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PartitionBasic.lean#L53-L58

module
public import Definitions.Def_CSeparatedNPComplete_PartitionDefs
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.dot_canon_e_le_dot_one {n : Nat} (a : Vec n) (i : Nat)
    (ha : is_vec_leq 0 a) : dot a (canon_e i) ≤ dot a 1 := by sorry
