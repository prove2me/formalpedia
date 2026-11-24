-- Prove2me | Theorems.Thm_BalanceSpecification_FiveSymbol_not_synchronized
-- name    : BalanceSpecification.FiveSymbol.not_synchronized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:11:07.119772+00:00
-- url     : https://prove2.me/theorems/4b8ae478-3dc5-4ff7-8ebb-1ff7b7d99eb9
-- title:
--   Five Symbol: not synchronized
-- statement:
--   The Five Symbol construction uses the not synchronized property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L558-L560
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L558-L560

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

theorem BalanceSpecification.FiveSymbol.not_synchronized : ¬ Synchronized shift := by sorry
