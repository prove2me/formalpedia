-- Prove2me | Theorems.Thm_BalanceSpecification_FiveSymbol_initialObstructions_card_le
-- name    : BalanceSpecification.FiveSymbol.initialObstructions_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:11:20.547793+00:00
-- url     : https://prove2.me/theorems/db944475-ff5d-4d19-98de-8f4a60f73680
-- title:
--   Five Symbol: initial Obstructions card le
-- statement:
--   The Five Symbol construction uses the initial Obstructions card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbolBalance.lean#L46-L55
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbolBalance.lean#L46-L55

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

theorem BalanceSpecification.FiveSymbol.initialObstructions_card_le {l : ℕ} (hl : 0 < l) :
    (initialObstructions l).card ≤ l := by sorry
