-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_getElem_reversedBlocks_mem_upperTexts
-- name    : DeciSigma1.Holes.Fresh.getElem_reversedBlocks_mem_upperTexts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:06:45.065988+00:00
-- url     : https://prove2.me/theorems/ce9014f4-8611-416e-ad1f-b147901c71ad
-- title:
--   Fresh: get Elem reversed Blocks mem upper Texts
-- statement:
--   Each lower block of a parse at level `t + 1` is an upper block of level `t`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L914-L921
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L914-L921

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

theorem DeciSigma1.Holes.Fresh.getElem_reversedBlocks_mem_upperTexts {t : ℕ} {o : Fin k × ℕ × ℕ}
    (ho : o ∈ upperOccurrences W (t + 1)) {d : ℕ} (hd : d < (reversedBlocks W (t + 1) o).length) :
    (reversedBlocks W (t + 1) o)[d] ∈ upperTexts W t := by sorry
