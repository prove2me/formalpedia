-- Prove2me | Theorems.Thm_BalanceSpecification_FiveSymbol_bad_follower_card_le_sum
-- name    : BalanceSpecification.FiveSymbol.bad_follower_card_le_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:11:57.933513+00:00
-- url     : https://prove2.me/theorems/23538e0f-5b5b-40b1-a8e4-53e1ea9b7f8f
-- title:
--   Five Symbol: bad follower card le sum
-- statement:
--   The Five Symbol construction uses the bad follower card le sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbolBalance.lean#L256-L275
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbolBalance.lean#L256-L275

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

theorem BalanceSpecification.FiveSymbol.bad_follower_card_le_sum {u : Word Alphabet} (hu : u ∈ language shift) (n : ℕ) :
    ((wordFinset (language shift) n) \ followerFinset (language shift) u n).card ≤
      ∑ l ∈ Finset.Icc 1 n, l * wordCount (language shift) (n - l) := by sorry
