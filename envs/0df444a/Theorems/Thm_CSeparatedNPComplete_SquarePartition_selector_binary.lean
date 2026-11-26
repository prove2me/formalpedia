-- Prove2me | Theorems.Thm_CSeparatedNPComplete_SquarePartition_selector_binary
-- name    : CSeparatedNPComplete.SquarePartition.selector_binary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:49:32.966404+00:00
-- url     : https://prove2.me/theorems/0c6814c0-a3f2-4337-a437-9a4dd14a900f
-- title:
--   Square Partition: selector binary
-- statement:
--   The Square Partition construction uses the selector binary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquarePartition.lean#L116-L124
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquarePartition.lean#L116-L124

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquarePartition

theorem CSeparatedNPComplete.SquarePartition.selector_binary (N : ℕ) (b : ℕ → Bool) : is_binary (selector N b) := by sorry
