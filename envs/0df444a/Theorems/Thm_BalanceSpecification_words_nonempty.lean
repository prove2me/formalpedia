-- Prove2me | Theorems.Thm_BalanceSpecification_words_nonempty
-- name    : BalanceSpecification.words_nonempty
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:16:48.174366+00:00
-- url     : https://prove2.me/theorems/3435b5f7-b89a-41a7-8972-d4b012569da7
-- title:
--   Balance Specification: words nonempty
-- statement:
--   Every nonempty shift has a word of every length, including zero.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/LanguageProperties.lean#L58-L60
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/LanguageProperties.lean#L58-L60

module
public import Definitions.Def_BalanceSpecificaton_Language
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*}
variable [TopologicalSpace A] {X : ShiftSpace A}

theorem BalanceSpecification.words_nonempty (hX : X.carrier.Nonempty) (n : ℕ) : (words X n).Nonempty := by sorry
