-- Prove2me | Theorems.Thm_BalanceSpecification_FiveSymbol_rightCrossingCover_card_le
-- name    : BalanceSpecification.FiveSymbol.rightCrossingCover_card_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:11:42.531813+00:00
-- url     : https://prove2.me/theorems/da9189a9-d4eb-47c8-b93b-4e019217f2c1
-- title:
--   Five Symbol: right Crossing Cover card le
-- statement:
--   The Five Symbol construction uses the right Crossing Cover card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbolBalance.lean#L193-L205
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbolBalance.lean#L193-L205

module
public import Definitions.Def_BalanceSpecificaton_FiveSymbol
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FiveSymbolBalance
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.FiveSymbol

theorem BalanceSpecification.FiveSymbol.rightCrossingCover_card_le (n : ℕ) {l : ℕ} (hl : 0 < l) :
    (rightCrossingCover n l).card ≤ l * wordCount (language shift) (n - l) := by sorry
