-- Prove2me | Theorems.Thm_CSeparatedNPComplete_SquarePartition_selector_is_ec_partition_iff
-- name    : CSeparatedNPComplete.SquarePartition.selector_is_ec_partition_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:49:55.542115+00:00
-- url     : https://prove2.me/theorems/9822b8dd-83dd-4475-9c4e-8f1592d32dbd
-- title:
--   Square Partition: selector is ec partition iff
-- statement:
--   The connection to the existing real-vector equal-cardinality predicate.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquarePartition.lean#L154-L169
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquarePartition.lean#L154-L169

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquarePartition

theorem CSeparatedNPComplete.SquarePartition.selector_is_ec_partition_iff (N : ℕ) (a : ℕ → ℕ) (K : ℕ) (b : ℕ → Bool) :
    is_ec_partition (selector N b) (values N a K) ↔
      leftSum N N a K b = rightSum N N a K b := by sorry
