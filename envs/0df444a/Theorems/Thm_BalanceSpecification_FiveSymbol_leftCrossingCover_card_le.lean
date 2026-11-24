-- Prove2me | Theorems.Thm_BalanceSpecification_FiveSymbol_leftCrossingCover_card_le
-- name    : BalanceSpecification.FiveSymbol.leftCrossingCover_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:11:41.039864+00:00
-- url     : https://prove2.me/theorems/064fc499-3438-445b-b09e-8f9d7d8fbd1f
-- title:
--   Five Symbol: left Crossing Cover card le
-- statement:
--   The Five Symbol construction uses the left Crossing Cover card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbolBalance.lean#L207-L219
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbolBalance.lean#L207-L219

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

theorem BalanceSpecification.FiveSymbol.leftCrossingCover_card_le (n : ℕ) {l : ℕ} (hl : 0 < l) :
    (leftCrossingCover n l).card ≤ l * wordCount (language shift) (n - l) := by sorry
