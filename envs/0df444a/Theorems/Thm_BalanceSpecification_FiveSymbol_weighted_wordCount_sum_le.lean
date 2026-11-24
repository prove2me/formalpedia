-- Prove2me | Theorems.Thm_BalanceSpecification_FiveSymbol_weighted_wordCount_sum_le
-- name    : BalanceSpecification.FiveSymbol.weighted_wordCount_sum_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:52:42.974781+00:00
-- url     : https://prove2.me/theorems/5de93bbb-9625-4370-a898-f1b2a085ce0c
-- title:
--   Five Symbol: weighted word Count sum le
-- statement:
--   The Five Symbol construction uses the weighted word Count sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbolBalance.lean#L336-L350
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbolBalance.lean#L336-L350

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

theorem BalanceSpecification.FiveSymbol.weighted_wordCount_sum_le (n : ℕ) :
    (∑ l ∈ Finset.Icc 1 n, (l : ℝ) * wordCount (language shift) (n - l)) ≤
      (4 / 9 : ℝ) * wordCount (language shift) n := by sorry
