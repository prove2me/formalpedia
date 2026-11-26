-- Prove2me | Theorems.Thm_CSeparatedNPComplete_SquarePartition_selected_sum
-- name    : CSeparatedNPComplete.SquarePartition.selected_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:49:36.420579+00:00
-- url     : https://prove2.me/theorems/2f2a5c03-1d95-4363-bb7f-048a509827e9
-- title:
--   Square Partition: selected sum
-- statement:
--   The Square Partition construction uses the selected sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquarePartition.lean#L135-L142
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquarePartition.lean#L135-L142

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquarePartition

theorem CSeparatedNPComplete.SquarePartition.selected_sum (N : ℕ) (a : ℕ → ℕ) (K : ℕ) (b : ℕ → Bool) :
    dot (selector N b) (values N a K) = (leftSum N N a K b : ℝ) := by sorry
