-- Prove2me | Theorems.Thm_CSeparatedNPComplete_exists_square_partition_implies_exists_partition
-- name    : CSeparatedNPComplete.exists_square_partition_implies_exists_partition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:55:45.553832+00:00
-- url     : https://prove2.me/theorems/50acf1fd-ead7-5c11-bc17-8c6b8db7fb6e
-- title:
--   CSeparated NPComplete: exists square partition implies exists partition
-- statement:
--   Existence of a paired-square partition implies existence of an original-weight partition.
--   The conclusion balances the original sums; it does not impose original cardinality.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquarePartitionResults.lean#L20-L26
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquarePartitionResults.lean#L20-L26

module
public import Definitions.Def_CSeparatedNPComplete_SquareReduction
public import Definitions.Def_CSeparatedNPComplete_SquarePartitionResults
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.exists_square_partition_implies_exists_partition
    (N : ℕ) (a : ℕ → ℕ) (K : ℕ)
    (hK : 1 ≤ K) (hbound : ∀ i, i < N → a i ≤ K ^ (2 * i))
    (h : ∃ b, SquarePartition.leftSum N N a K b = SquarePartition.rightSum N N a K b) :
    ∃ b, SquarePartition.chooseSum N a b = SquarePartition.chooseSum N a (fun i => !(b i)) := by sorry
