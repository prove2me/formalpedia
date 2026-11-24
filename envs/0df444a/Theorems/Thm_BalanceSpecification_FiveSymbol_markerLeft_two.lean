-- Prove2me | Theorems.Thm_BalanceSpecification_FiveSymbol_markerLeft_two
-- name    : BalanceSpecification.FiveSymbol.markerLeft_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:52:15.888983+00:00
-- url     : https://prove2.me/theorems/621d1f74-0f89-4220-8b86-b392b4ce8e1d
-- title:
--   Five Symbol: marker Left two
-- statement:
--   The Five Symbol construction uses the marker Left two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L371-L376
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L371-L376

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

theorem BalanceSpecification.FiveSymbol.markerLeft_two (j : ℕ) :
    (markerLeft j)[markerLength j + 1]'(by rw [length_markerLeft]; omega) = 2 := by sorry
