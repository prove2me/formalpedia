-- Prove2me | Theorems.Thm_CSeparatedNPComplete_SquarePartition_total_sum
-- name    : CSeparatedNPComplete.SquarePartition.total_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:49:40.481345+00:00
-- url     : https://prove2.me/theorems/65337f5b-649c-5b82-ba44-429d539b2b79
-- title:
--   Square Partition: total sum
-- statement:
--   The Square Partition construction uses the total sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquarePartition.lean#L144-L151
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquarePartition.lean#L144-L151

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquarePartition

theorem CSeparatedNPComplete.SquarePartition.total_sum (N : ℕ) (a : ℕ → ℕ) (K : ℕ) (b : ℕ → Bool) :
    dot (values N a K) 1 = (leftSum N N a K b : ℝ) + (rightSum N N a K b : ℝ) := by sorry
