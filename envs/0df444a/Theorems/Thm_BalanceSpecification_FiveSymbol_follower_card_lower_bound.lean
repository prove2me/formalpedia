-- Prove2me | Theorems.Thm_BalanceSpecification_FiveSymbol_follower_card_lower_bound
-- name    : BalanceSpecification.FiveSymbol.follower_card_lower_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:12:06.554368+00:00
-- url     : https://prove2.me/theorems/ba38a27b-ff5d-46ba-a8c1-8f3d8b969e12
-- title:
--   Five Symbol: follower card lower bound
-- statement:
--   At least five ninths of all words follow every admissible word.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbolBalance.lean#L353-L370
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbolBalance.lean#L353-L370

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

theorem BalanceSpecification.FiveSymbol.follower_card_lower_bound {u : Word Alphabet} (hu : u ∈ language shift) (n : ℕ) :
    (5 / 9 : ℝ) * wordCount (language shift) n ≤
      (followerFinset (language shift) u n).card := by sorry
