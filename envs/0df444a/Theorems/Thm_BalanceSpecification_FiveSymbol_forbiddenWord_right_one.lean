-- Prove2me | Theorems.Thm_BalanceSpecification_FiveSymbol_forbiddenWord_right_one
-- name    : BalanceSpecification.FiveSymbol.forbiddenWord_right_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:52:08.728938+00:00
-- url     : https://prove2.me/theorems/fefb5140-581c-45af-b8b8-de4408100334
-- title:
--   Five Symbol: forbidden Word right one
-- statement:
--   The Five Symbol construction uses the forbidden Word right one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L261-L271
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L261-L271

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

theorem BalanceSpecification.FiveSymbol.forbiddenWord_right_one (j : ℕ) {i : ℕ} (hi : i < markerLength j) :
    (forbiddenWord j)[rightOffset j + (i + 1)]'(by
      rw [forbiddenWord_length_rightOffset]; omega) = 1 := by sorry
