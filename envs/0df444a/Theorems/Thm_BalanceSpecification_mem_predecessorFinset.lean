-- Prove2me | Theorems.Thm_BalanceSpecification_mem_predecessorFinset
-- name    : BalanceSpecification.mem_predecessorFinset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:30:41.906891+00:00
-- url     : https://prove2.me/theorems/4c9b971e-8248-4432-a198-c3d280bd28a8
-- title:
--   Balance Specification: mem predecessor Finset
-- statement:
--   The Balance Specification construction uses the mem predecessor Finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Counting.lean#L59-L62
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Counting.lean#L59-L62

module
public import Definitions.Def_BalanceSpecificaton_Language
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Counting
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*} [Fintype A]

theorem BalanceSpecification.mem_predecessorFinset {L : Set (Word A)} {u w : Word A} {n : ℕ} :
    w ∈ predecessorFinset L u n ↔ w ∈ L ∧ w.length = n ∧ w ++ u ∈ L := by sorry
