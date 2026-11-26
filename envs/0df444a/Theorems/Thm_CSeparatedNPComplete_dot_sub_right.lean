-- Prove2me | Theorems.Thm_CSeparatedNPComplete_dot_sub_right
-- name    : CSeparatedNPComplete.dot_sub_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:51:16.953419+00:00
-- url     : https://prove2.me/theorems/2cdc7adf-e79f-42c0-99ed-2519e5d5b70d
-- title:
--   CSeparated NPComplete: dot sub right
-- statement:
--   The CSeparated NPComplete construction uses the dot sub right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PartitionBasic.lean#L28-L30
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PartitionBasic.lean#L28-L30

module
public import Definitions.Def_CSeparatedNPComplete_PartitionDefs
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.dot_sub_right {n : Nat} (a u v : Vec n) :
    dot a (u - v) = dot a u - dot a v := by sorry
