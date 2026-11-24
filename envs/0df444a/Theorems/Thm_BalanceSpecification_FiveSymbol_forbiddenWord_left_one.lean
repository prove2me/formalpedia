-- Prove2me | Theorems.Thm_BalanceSpecification_FiveSymbol_forbiddenWord_left_one
-- name    : BalanceSpecification.FiveSymbol.forbiddenWord_left_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:51:44.738993+00:00
-- url     : https://prove2.me/theorems/2645e4cb-3ebd-448e-937b-51e81e7e3fd0
-- title:
--   Five Symbol: forbidden Word left one
-- statement:
--   The Five Symbol construction uses the forbidden Word left one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L235-L243
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L235-L243

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

theorem BalanceSpecification.FiveSymbol.forbiddenWord_left_one (j : ℕ) {i : ℕ} (hi : i < markerLength j) :
    (forbiddenWord j)[i + 1]'(by rw [length_forbiddenWord]; omega) = 1 := by sorry
