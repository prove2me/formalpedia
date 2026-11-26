-- Prove2me | Theorems.Thm_CSeparatedNPComplete_dot_canon_e_nonneg
-- name    : CSeparatedNPComplete.dot_canon_e_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:46:45.668501+00:00
-- url     : https://prove2.me/theorems/06153cf8-4632-480b-b498-271a0a79a0e3
-- title:
--   CSeparated NPComplete: dot canon e nonneg
-- statement:
--   The CSeparated NPComplete construction uses the dot canon e nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PartitionBasic.lean#L46-L51
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PartitionBasic.lean#L46-L51

module
public import Definitions.Def_CSeparatedNPComplete_PartitionDefs
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.dot_canon_e_nonneg {n : Nat} (a : Vec n) (i : Nat)
    (ha : is_vec_leq 0 a) : 0 ≤ dot a (canon_e i) := by sorry
