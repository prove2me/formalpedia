-- Prove2me | Theorems.Thm_BalanceSpecification_mem_wordFinset
-- name    : BalanceSpecification.mem_wordFinset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:30:40.173832+00:00
-- url     : https://prove2.me/theorems/81589586-f288-4598-bd58-4c778dc7e496
-- title:
--   Balance Specification: mem word Finset
-- statement:
--   The Balance Specification construction uses the mem word Finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Counting.lean#L39-L42
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Counting.lean#L39-L42

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

theorem BalanceSpecification.mem_wordFinset {L : Set (Word A)} {w : Word A} {n : ℕ} :
    w ∈ wordFinset L n ↔ w ∈ L ∧ w.length = n := by sorry
