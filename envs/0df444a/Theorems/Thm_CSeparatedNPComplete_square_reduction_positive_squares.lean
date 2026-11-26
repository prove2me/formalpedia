-- Prove2me | Theorems.Thm_CSeparatedNPComplete_square_reduction_positive_squares
-- name    : CSeparatedNPComplete.square_reduction_positive_squares
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:55:54.159923+00:00
-- url     : https://prove2.me/theorems/4c494c64-bf49-5afe-9ff3-da526f194ef7
-- title:
--   CSeparated NPComplete: square reduction positive squares
-- statement:
--   Every output coordinate of the unconditional reduction is a strictly
--   positive natural square.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquarePartitionResults.lean#L49-L52
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquarePartitionResults.lean#L49-L52

module
public import Definitions.Def_CSeparatedNPComplete_SquareReduction
public import Definitions.Def_CSeparatedNPComplete_SquarePartitionResults
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.square_reduction_positive_squares (n : ℕ) (a : Fin n → ℕ) :
    perf_square_vec (SquareReduction.values a) ∧
      ∀ i, 0 < SquareReduction.values a i := by sorry
