-- Prove2me | Theorems.Thm_BalanceSpecification_FiveSymbol_forbiddenWord_get_last
-- name    : BalanceSpecification.FiveSymbol.forbiddenWord_get_last
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:51:42.265105+00:00
-- url     : https://prove2.me/theorems/56ac6a92-e8be-4b02-a4ba-fe256f9f7a93
-- title:
--   Five Symbol: forbidden Word get last
-- statement:
--   The Five Symbol construction uses the forbidden Word get last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L67-L78
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L67-L78

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

theorem BalanceSpecification.FiveSymbol.forbiddenWord_get_last (j : ℕ) :
    (forbiddenWord j)[(forbiddenWord j).length - 1]'(by
      have := forbiddenWord_length_pos j; omega) = 4 := by sorry
