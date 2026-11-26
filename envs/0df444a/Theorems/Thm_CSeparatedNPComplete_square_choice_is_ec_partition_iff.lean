-- Prove2me | Theorems.Thm_CSeparatedNPComplete_square_choice_is_ec_partition_iff
-- name    : CSeparatedNPComplete.square_choice_is_ec_partition_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:56:00.574032+00:00
-- url     : https://prove2.me/theorems/0c7bcc58-3af8-4e6d-9c8c-fca7d17b345c
-- title:
--   CSeparated NPComplete: square choice is ec partition iff
-- statement:
--   A paired Boolean choice yields an equal-cardinality partition of the square
--   vector exactly when it balances the original weights. Every coordinate of this
--   vector is a natural square, by `SquarePartition.values_perfect_square`.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquarePartitionResults.lean#L39-L45
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquarePartitionResults.lean#L39-L45

module
public import Definitions.Def_CSeparatedNPComplete_SquareReduction
public import Definitions.Def_CSeparatedNPComplete_SquarePartitionResults
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.square_choice_is_ec_partition_iff
    (N : ℕ) (a : ℕ → ℕ) (K : ℕ) (b : ℕ → Bool)
    (hK : 1 ≤ K) (hbound : ∀ i, i < N → a i ≤ K ^ (2 * i)) :
    is_ec_partition (SquarePartition.selector N b) (SquarePartition.values N a K) ↔
      SquarePartition.chooseSum N a b = SquarePartition.chooseSum N a (fun i => !(b i)) := by sorry
