-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_reversedBlocks_zero_length_one
-- name    : DeciSigma1.Holes.Fresh.reversedBlocks_zero_length_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:06:43.772233+00:00
-- url     : https://prove2.me/theorems/2848bc3d-9cfa-4ed3-b058-94c8305e7973
-- title:
--   Fresh: reversed Blocks zero length one
-- statement:
--   The Fresh construction uses the reversed Blocks zero length one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L900-L911
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L900-L911

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Bound
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α}
variable {S : Type} [Fintype S] [DecidableEq S] {T : Table α S k}

theorem DeciSigma1.Holes.Fresh.reversedBlocks_zero_length_one {o : Fin k × ℕ × ℕ}
    (ho : o ∈ upperOccurrences W 0) {d : ℕ} (hd : d < (reversedBlocks W 0 o).length) :
    ((reversedBlocks W 0 o)[d]).length = 1 := by sorry
