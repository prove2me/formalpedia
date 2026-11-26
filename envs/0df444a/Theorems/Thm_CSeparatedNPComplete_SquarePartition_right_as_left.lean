-- Prove2me | Theorems.Thm_CSeparatedNPComplete_SquarePartition_right_as_left
-- name    : CSeparatedNPComplete.SquarePartition.right_as_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:49:18.835086+00:00
-- url     : https://prove2.me/theorems/55be33ab-54fe-5f9a-b690-5f2135bc70ee
-- title:
--   Square Partition: right as left
-- statement:
--   The Square Partition construction uses the right as left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquarePartition.lean#L66-L70
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquarePartition.lean#L66-L70

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquarePartition

theorem CSeparatedNPComplete.SquarePartition.right_as_left (N m : ℕ) (a : ℕ → ℕ) (K : ℕ) (b : ℕ → Bool) :
    rightSum N m a K b = leftSum N m a K (fun i => !(b i)) := by sorry
