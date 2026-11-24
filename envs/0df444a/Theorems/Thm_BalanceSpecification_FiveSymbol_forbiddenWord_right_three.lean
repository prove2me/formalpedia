-- Prove2me | Theorems.Thm_BalanceSpecification_FiveSymbol_forbiddenWord_right_three
-- name    : BalanceSpecification.FiveSymbol.forbiddenWord_right_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:52:10.454133+00:00
-- url     : https://prove2.me/theorems/8a9df42e-d886-448a-bf40-37eaa1a3a8f6
-- title:
--   Five Symbol: forbidden Word right three
-- statement:
--   The Five Symbol construction uses the forbidden Word right three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L253-L259
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L253-L259

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

theorem BalanceSpecification.FiveSymbol.forbiddenWord_right_three (j : ℕ) :
    (forbiddenWord j)[rightOffset j]'(by rw [forbiddenWord_length_rightOffset]; omega) = 3 := by sorry
