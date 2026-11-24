-- Prove2me | Theorems.Thm_BalanceSpecification_FiveSymbol_markerLeft_one
-- name    : BalanceSpecification.FiveSymbol.markerLeft_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:10:34.880495+00:00
-- url     : https://prove2.me/theorems/7a974d08-def1-4c8b-a898-219a0c396a99
-- title:
--   Five Symbol: marker Left one
-- statement:
--   The Five Symbol construction uses the marker Left one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L364-L369
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L364-L369

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

theorem BalanceSpecification.FiveSymbol.markerLeft_one (j : ℕ) {i : ℕ} (hi : i < markerLength j) :
    (markerLeft j)[i + 1]'(by rw [length_markerLeft]; omega) = 1 := by sorry
