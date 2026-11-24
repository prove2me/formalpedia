-- Prove2me | Theorems.Thm_BalanceSpecification_FiveSymbol_singleton_four_suffix_forbiddenWord
-- name    : BalanceSpecification.FiveSymbol.singleton_four_suffix_forbiddenWord
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:10:01.989147+00:00
-- url     : https://prove2.me/theorems/747aa982-cd0c-471b-af6a-22e63f4371b5
-- title:
--   Five Symbol: singleton four suffix forbidden Word
-- statement:
--   The Five Symbol construction uses the singleton four suffix forbidden Word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L161-L165
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L161-L165

module
public import Definitions.Def_BalanceSpecificaton_Shortlex
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FiveSymbol
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.FiveSymbol

theorem BalanceSpecification.FiveSymbol.singleton_four_suffix_forbiddenWord (j : ℕ) :
    ([4] : Word Alphabet) <:+ forbiddenWord j := by sorry
