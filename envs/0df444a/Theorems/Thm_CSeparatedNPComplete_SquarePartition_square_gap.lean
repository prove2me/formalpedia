-- Prove2me | Theorems.Thm_CSeparatedNPComplete_SquarePartition_square_gap
-- name    : CSeparatedNPComplete.SquarePartition.square_gap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:49:24.566341+00:00
-- url     : https://prove2.me/theorems/e6a974cc-4af6-4c90-80db-f24dc26cf15d
-- title:
--   Square Partition: square gap
-- statement:
--   The Square Partition construction uses the square gap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquarePartition.lean#L41-L44
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquarePartition.lean#L41-L44

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquarePartition

theorem CSeparatedNPComplete.SquarePartition.square_gap (u v : ℕ) (h : v ≤ u) :
    (u + v) ^ 2 = (u - v) ^ 2 + 4 * u * v := by sorry
