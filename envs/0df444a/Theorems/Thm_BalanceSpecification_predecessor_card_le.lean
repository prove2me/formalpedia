-- Prove2me | Theorems.Thm_BalanceSpecification_predecessor_card_le
-- name    : BalanceSpecification.predecessor_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:50:38.204523+00:00
-- url     : https://prove2.me/theorems/4882ce9a-393b-4671-9aa6-61df26dd91c4
-- title:
--   Balance Specification: predecessor card le
-- statement:
--   The Balance Specification construction uses the predecessor card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Counting.lean#L84-L87
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Counting.lean#L84-L87

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

theorem BalanceSpecification.predecessor_card_le (L : Set (Word A)) (u : Word A) (n : ℕ) :
    (predecessorFinset L u n).card ≤ wordCount L n := by sorry
