-- Prove2me | Theorems.Thm_CSeparatedNPComplete_dot_const
-- name    : CSeparatedNPComplete.dot_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:51:16.465797+00:00
-- url     : https://prove2.me/theorems/56695edd-203f-4437-9662-7aea396b0187
-- title:
--   CSeparated NPComplete: dot const
-- statement:
--   The CSeparated NPComplete construction uses the dot const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PartitionBasic.lean#L10-L15
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PartitionBasic.lean#L10-L15

module
public import Definitions.Def_CSeparatedNPComplete_PartitionDefs
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.dot_const {n : Nat} (a : Vec n) (r : ℝ) :
    dot a (fun _ => r) = r * dot a 1 := by sorry
