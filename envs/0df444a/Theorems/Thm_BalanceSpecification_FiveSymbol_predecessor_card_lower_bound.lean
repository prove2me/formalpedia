-- Prove2me | Theorems.Thm_BalanceSpecification_FiveSymbol_predecessor_card_lower_bound
-- name    : BalanceSpecification.FiveSymbol.predecessor_card_lower_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:12:12.552609+00:00
-- url     : https://prove2.me/theorems/802035a6-9212-4075-ae88-116622d39967
-- title:
--   Five Symbol: predecessor card lower bound
-- statement:
--   At least five ninths of all words precede every admissible word.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbolBalance.lean#L373-L390
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbolBalance.lean#L373-L390

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

theorem BalanceSpecification.FiveSymbol.predecessor_card_lower_bound {u : Word Alphabet} (hu : u ∈ language shift) (n : ℕ) :
    (5 / 9 : ℝ) * wordCount (language shift) n ≤
      (predecessorFinset (language shift) u n).card := by sorry
