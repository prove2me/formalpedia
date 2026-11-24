-- Prove2me | Theorems.Thm_BalanceSpecification_FiveSymbol_markerRight_three
-- name    : BalanceSpecification.FiveSymbol.markerRight_three
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:10:47.781586+00:00
-- url     : https://prove2.me/theorems/eb9a1499-4fc2-4c2f-9203-5cb8f96cf91f
-- title:
--   Five Symbol: marker Right three
-- statement:
--   The Five Symbol construction uses the marker Right three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L439-L441
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L439-L441

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

theorem BalanceSpecification.FiveSymbol.markerRight_three (j : ℕ) :
    (markerRight j)[0]'(by rw [length_markerRight]; omega) = 3 := by sorry
