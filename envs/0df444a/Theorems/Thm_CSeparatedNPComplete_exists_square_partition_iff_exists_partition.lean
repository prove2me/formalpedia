-- Prove2me | Theorems.Thm_CSeparatedNPComplete_exists_square_partition_iff_exists_partition
-- name    : CSeparatedNPComplete.exists_square_partition_iff_exists_partition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:55:59.940168+00:00
-- url     : https://prove2.me/theorems/6c4cd410-5c5d-4b1f-9f90-d74ec1303b94
-- title:
--   CSeparated NPComplete: exists square partition iff exists partition
-- statement:
--   The paired-choice result also holds in the forward direction.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquarePartitionResults.lean#L29-L34
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquarePartitionResults.lean#L29-L34

module
public import Definitions.Def_CSeparatedNPComplete_SquareReduction
public import Definitions.Def_CSeparatedNPComplete_SquarePartitionResults
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.exists_square_partition_iff_exists_partition
    (N : ℕ) (a : ℕ → ℕ) (K : ℕ)
    (hK : 1 ≤ K) (hbound : ∀ i, i < N → a i ≤ K ^ (2 * i)) :
    (∃ b, SquarePartition.leftSum N N a K b = SquarePartition.rightSum N N a K b) ↔
      ∃ b, SquarePartition.chooseSum N a b = SquarePartition.chooseSum N a (fun i => !(b i)) := by sorry
