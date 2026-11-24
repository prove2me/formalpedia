-- Prove2me | Theorems.Thm_BalanceSpecification_FiveSymbol_forbiddenWord_left_two
-- name    : BalanceSpecification.FiveSymbol.forbiddenWord_left_two
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:10:42.366614+00:00
-- url     : https://prove2.me/theorems/c122720f-0003-47c8-b3c7-941be6a7d7b7
-- title:
--   Five Symbol: forbidden Word left two
-- statement:
--   The Five Symbol construction uses the forbidden Word left two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L378-L384
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L378-L384

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

theorem BalanceSpecification.FiveSymbol.forbiddenWord_left_two (j : ℕ) :
    (forbiddenWord j)[markerLength j + 1]'(by rw [length_forbiddenWord]; omega) = 2 := by sorry
