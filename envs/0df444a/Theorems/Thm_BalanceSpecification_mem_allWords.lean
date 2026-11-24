-- Prove2me | Theorems.Thm_BalanceSpecification_mem_allWords
-- name    : BalanceSpecification.mem_allWords
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:30:45.42163+00:00
-- url     : https://prove2.me/theorems/72b99205-6507-4913-9334-0edcb4e7e506
-- title:
--   Balance Specification: mem all Words
-- statement:
--   The Balance Specification construction uses the mem all Words property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Counting.lean#L24-L32
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Counting.lean#L24-L32

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

theorem BalanceSpecification.mem_allWords {w : Word A} {n : ℕ} :
    w ∈ allWords n ↔ w.length = n := by sorry
