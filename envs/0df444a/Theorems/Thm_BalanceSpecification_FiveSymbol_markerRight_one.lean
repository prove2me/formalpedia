-- Prove2me | Theorems.Thm_BalanceSpecification_FiveSymbol_markerRight_one
-- name    : BalanceSpecification.FiveSymbol.markerRight_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:10:49.511333+00:00
-- url     : https://prove2.me/theorems/8485472d-a6a6-4b11-8243-278c93b30970
-- title:
--   Five Symbol: marker Right one
-- statement:
--   The Five Symbol construction uses the marker Right one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L443-L448
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L443-L448

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

theorem BalanceSpecification.FiveSymbol.markerRight_one (j : ℕ) {i : ℕ} (hi : i < markerLength j) :
    (markerRight j)[i + 1]'((length_markerRight j).symm ▸ Nat.lt_succ_of_lt (Nat.succ_lt_succ hi)) = 1 := by sorry
