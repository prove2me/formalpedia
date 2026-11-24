-- Prove2me | Theorems.Thm_BalanceSpecification_FiveSymbol_bad_predecessor_card_le_sum
-- name    : BalanceSpecification.FiveSymbol.bad_predecessor_card_le_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:11:57.612819+00:00
-- url     : https://prove2.me/theorems/f1630275-eea8-4b41-84cd-038d9c075ac2
-- title:
--   Five Symbol: bad predecessor card le sum
-- statement:
--   The Five Symbol construction uses the bad predecessor card le sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbolBalance.lean#L277-L296
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbolBalance.lean#L277-L296

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

theorem BalanceSpecification.FiveSymbol.bad_predecessor_card_le_sum {u : Word Alphabet} (hu : u ∈ language shift) (n : ℕ) :
    ((wordFinset (language shift) n) \ predecessorFinset (language shift) u n).card ≤
      ∑ l ∈ Finset.Icc 1 n, l * wordCount (language shift) (n - l) := by sorry
