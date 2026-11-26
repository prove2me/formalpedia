-- Prove2me | Theorems.Thm_CSeparatedNPComplete_SquarePartition_values_perfect_square
-- name    : CSeparatedNPComplete.SquarePartition.values_perfect_square
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:47:20.166269+00:00
-- url     : https://prove2.me/theorems/902966d3-fe56-448a-9893-7cebd7846b01
-- title:
--   Square Partition: values perfect square
-- statement:
--   The Square Partition construction uses the values perfect square property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquarePartition.lean#L103-L114
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquarePartition.lean#L103-L114

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquarePartition

theorem CSeparatedNPComplete.SquarePartition.values_perfect_square (N : ℕ) (a : ℕ → ℕ) (K : ℕ) :
    perf_square_vec (values N a K) := by sorry
