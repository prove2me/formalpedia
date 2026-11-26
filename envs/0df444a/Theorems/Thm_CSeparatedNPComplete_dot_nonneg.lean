-- Prove2me | Theorems.Thm_CSeparatedNPComplete_dot_nonneg
-- name    : CSeparatedNPComplete.dot_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:46:49.610058+00:00
-- url     : https://prove2.me/theorems/314928d0-cf18-4185-9e36-0a266d905d33
-- title:
--   CSeparated NPComplete: dot nonneg
-- statement:
--   The CSeparated NPComplete construction uses the dot nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PartitionBasic.lean#L32-L34
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PartitionBasic.lean#L32-L34

module
public import Definitions.Def_CSeparatedNPComplete_PartitionDefs
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.dot_nonneg {n : Nat} {a v : Vec n}
    (ha : is_vec_leq 0 a) (hv : is_vec_leq 0 v) : 0 ≤ dot a v := by sorry
