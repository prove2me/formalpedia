-- Prove2me | Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
-- name    : BalanceSpecification.wordCount_reverseLanguage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:31:10.664516+00:00
-- url     : https://prove2.me/theorems/a09bf6e6-3e4c-4ab9-9bcf-bf1de249b4dc
-- title:
--   Balance Specification: word Count reverse Language
-- statement:
--   The Balance Specification construction uses the word Count reverse Language property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/CountBounds.lean#L139-L154
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/CountBounds.lean#L139-L154

module
public import Definitions.Def_BalanceSpecificaton_Counting
public import Mathlib.Data.Finset.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_CountBounds
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*} [Fintype A] {L : Set (Word A)}

theorem BalanceSpecification.wordCount_reverseLanguage (L : Set (Word A)) (n : ℕ) :
    wordCount (reverseLanguage L) n = wordCount L n := by sorry
