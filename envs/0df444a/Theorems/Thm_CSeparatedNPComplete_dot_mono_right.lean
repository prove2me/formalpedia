-- Prove2me | Theorems.Thm_CSeparatedNPComplete_dot_mono_right
-- name    : CSeparatedNPComplete.dot_mono_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:46:48.358003+00:00
-- url     : https://prove2.me/theorems/36702a1c-8bce-5900-ac57-5047e51bfe7f
-- title:
--   CSeparated NPComplete: dot mono right
-- statement:
--   The CSeparated NPComplete construction uses the dot mono right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PartitionBasic.lean#L36-L38
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PartitionBasic.lean#L36-L38

module
public import Definitions.Def_CSeparatedNPComplete_PartitionDefs
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.dot_mono_right {n : Nat} {a u v : Vec n}
    (ha : is_vec_leq 0 a) (huv : is_vec_leq u v) : dot a u ≤ dot a v := by sorry
