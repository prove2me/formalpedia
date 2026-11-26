-- Prove2me | Theorems.Thm_CSeparatedNPComplete_square_partition_implies_partition_for_choice
-- name    : CSeparatedNPComplete.square_partition_implies_partition_for_choice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:50:22.088712+00:00
-- url     : https://prove2.me/theorems/7cb66a59-7842-5da4-98e7-d89cdfde7302
-- title:
--   CSeparated NPComplete: square partition implies partition for choice
-- statement:
--   A paired-square partition implies a partition of the original weights.
--   The square partition here chooses exactly one square from each constructed pair.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquarePartitionResults.lean#L11-L16
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquarePartitionResults.lean#L11-L16

module
public import Definitions.Def_CSeparatedNPComplete_SquareReduction
public import Definitions.Def_CSeparatedNPComplete_SquarePartitionResults
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.square_partition_implies_partition_for_choice
    (N : ℕ) (a : ℕ → ℕ) (K : ℕ) (b : ℕ → Bool)
    (hK : 1 ≤ K) (hbound : ∀ i, i < N → a i ≤ K ^ (2 * i))
    (h : SquarePartition.leftSum N N a K b = SquarePartition.rightSum N N a K b) :
    SquarePartition.chooseSum N a b = SquarePartition.chooseSum N a (fun i => !(b i)) := by sorry
