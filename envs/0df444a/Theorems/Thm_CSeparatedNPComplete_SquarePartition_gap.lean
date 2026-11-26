-- Prove2me | Theorems.Thm_CSeparatedNPComplete_SquarePartition_gap
-- name    : CSeparatedNPComplete.SquarePartition.gap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:49:26.466734+00:00
-- url     : https://prove2.me/theorems/8c0f3f05-6d64-4358-aa3a-50e5bb2fe64c
-- title:
--   Square Partition: gap
-- statement:
--   The Square Partition construction uses the gap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquarePartition.lean#L58-L64
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquarePartition.lean#L58-L64

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquarePartition

theorem CSeparatedNPComplete.SquarePartition.gap (N : ℕ) (a : ℕ → ℕ) (K i : ℕ) (hi : i < N)
    (ha : a i ≤ K ^ (2 * i)) :
    plus N a K i = minus N a K i + 4 * K ^ (2 * N) * a i := by sorry
