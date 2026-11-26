-- Prove2me | Theorems.Thm_CSeparatedNPComplete_SquarePartition_left_decomp
-- name    : CSeparatedNPComplete.SquarePartition.left_decomp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:49:29.149906+00:00
-- url     : https://prove2.me/theorems/bb933274-60bc-5d6a-8525-b161b9694c11
-- title:
--   Square Partition: left decomp
-- statement:
--   The Square Partition construction uses the left decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquarePartition.lean#L72-L81
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquarePartition.lean#L72-L81

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquarePartition

theorem CSeparatedNPComplete.SquarePartition.left_decomp (N m : ℕ) (a : ℕ → ℕ) (K : ℕ) (b : ℕ → Bool)
    (hm : m ≤ N) (hbound : ∀ i, i < m → a i ≤ K ^ (2 * i)) :
    leftSum N m a K b = (∑ i : Fin m, minus N a K i) +
      4 * K ^ (2 * N) * chooseSum m a b := by sorry
