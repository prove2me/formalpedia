-- Prove2me | Theorems.Thm_CSeparatedNPComplete_SquarePartition_root_product
-- name    : CSeparatedNPComplete.SquarePartition.root_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:47:03.29688+00:00
-- url     : https://prove2.me/theorems/64809ad5-fa74-500c-b481-9fcbf6ceed65
-- title:
--   Square Partition: root product
-- statement:
--   The Square Partition construction uses the root product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquarePartition.lean#L52-L56
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquarePartition.lean#L52-L56

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquarePartition

theorem CSeparatedNPComplete.SquarePartition.root_product (N K i ai : ℕ) (hi : i ≤ N) :
    K ^ (N + i) * (ai * K ^ (N - i)) = ai * K ^ (2 * N) := by sorry
