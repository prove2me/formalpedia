-- Prove2me | Theorems.Thm_CSeparatedNPComplete_SquarePartition_for_choice_iff
-- name    : CSeparatedNPComplete.SquarePartition.for_choice_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:47:08.704597+00:00
-- url     : https://prove2.me/theorems/5ff32b89-8cfb-5bd2-ac6f-3c9ad5f47de6
-- title:
--   Square Partition: for choice iff
-- statement:
--   Both directions hold for choices that take one square from every pair.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquarePartition.lean#L84-L91
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquarePartition.lean#L84-L91

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquarePartition

theorem CSeparatedNPComplete.SquarePartition.for_choice_iff (N : ℕ) (a : ℕ → ℕ) (K : ℕ) (b : ℕ → Bool)
    (hK : 1 ≤ K) (hbound : ∀ i, i < N → a i ≤ K ^ (2 * i)) :
    leftSum N N a K b = rightSum N N a K b ↔
      chooseSum N a b = chooseSum N a (fun i => !(b i)) := by sorry
