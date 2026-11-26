-- Prove2me | Theorems.Thm_CSeparatedNPComplete_SquarePartition_upper_bound_root
-- name    : CSeparatedNPComplete.SquarePartition.upper_bound_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:49:19.318866+00:00
-- url     : https://prove2.me/theorems/10132659-db02-54b1-9e92-31de34c43d87
-- title:
--   Square Partition: upper bound root
-- statement:
--   The Square Partition construction uses the upper bound root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquarePartition.lean#L46-L50
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquarePartition.lean#L46-L50

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquarePartition

theorem CSeparatedNPComplete.SquarePartition.upper_bound_root (N K i ai : ℕ) (hi : i ≤ N)
    (ha : ai ≤ K ^ (2 * i)) : ai * K ^ (N - i) ≤ K ^ (N + i) := by sorry
