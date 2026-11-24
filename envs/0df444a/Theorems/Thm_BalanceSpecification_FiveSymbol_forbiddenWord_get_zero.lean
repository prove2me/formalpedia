-- Prove2me | Theorems.Thm_BalanceSpecification_FiveSymbol_forbiddenWord_get_zero
-- name    : BalanceSpecification.FiveSymbol.forbiddenWord_get_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:51:36.400622+00:00
-- url     : https://prove2.me/theorems/3e86d909-3728-4786-9dfe-61b27d4915dc
-- title:
--   Five Symbol: forbidden Word get zero
-- statement:
--   The Five Symbol construction uses the forbidden Word get zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L62-L65
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L62-L65

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

theorem BalanceSpecification.FiveSymbol.forbiddenWord_get_zero (j : ℕ) :
    (forbiddenWord j)[0]'(forbiddenWord_length_pos j) = 0 := by sorry
