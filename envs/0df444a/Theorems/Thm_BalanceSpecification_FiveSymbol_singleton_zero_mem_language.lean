-- Prove2me | Theorems.Thm_BalanceSpecification_FiveSymbol_singleton_zero_mem_language
-- name    : BalanceSpecification.FiveSymbol.singleton_zero_mem_language
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:11:05.321879+00:00
-- url     : https://prove2.me/theorems/fae167d4-98ee-4372-bfce-d05a19cc8b6a
-- title:
--   Five Symbol: singleton zero mem language
-- statement:
--   The alphabet symbol `0` is admissible.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L542-L547
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L542-L547

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

theorem BalanceSpecification.FiveSymbol.singleton_zero_mem_language : ([0] : Word Alphabet) ∈ language shift := by sorry
