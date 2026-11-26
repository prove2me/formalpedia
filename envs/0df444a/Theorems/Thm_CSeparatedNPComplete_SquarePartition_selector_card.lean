-- Prove2me | Theorems.Thm_CSeparatedNPComplete_SquarePartition_selector_card
-- name    : CSeparatedNPComplete.SquarePartition.selector_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:49:42.068218+00:00
-- url     : https://prove2.me/theorems/e517ad70-5a84-4ff3-9fbe-a68ee4361d81
-- title:
--   Square Partition: selector card
-- statement:
--   The Square Partition construction uses the selector card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquarePartition.lean#L126-L133
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquarePartition.lean#L126-L133

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquarePartition

theorem CSeparatedNPComplete.SquarePartition.selector_card (N : ℕ) (b : ℕ → Bool) : dot (selector N b) 1 = (N : ℝ) := by sorry
