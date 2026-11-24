-- Prove2me | Theorems.Thm_BalanceSpecification_FiveSymbol_not_isSynchronizing_of_ne_nil
-- name    : BalanceSpecification.FiveSymbol.not_isSynchronizing_of_ne_nil
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:10:59.876122+00:00
-- url     : https://prove2.me/theorems/ae96c6e6-5bdc-4f2a-a533-38b688a25208
-- title:
--   Five Symbol: not is Synchronizing of ne nil
-- statement:
--   No nonempty allowed word can synchronize the example.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L527-L539
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L527-L539

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

theorem BalanceSpecification.FiveSymbol.not_isSynchronizing_of_ne_nil {w : Word Alphabet}
    (hw : w ∈ language shift) (hwne : w ≠ []) : ¬ IsSynchronizing (language shift) w := by sorry
