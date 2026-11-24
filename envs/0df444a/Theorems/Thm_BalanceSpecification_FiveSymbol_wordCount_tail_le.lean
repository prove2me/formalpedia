-- Prove2me | Theorems.Thm_BalanceSpecification_FiveSymbol_wordCount_tail_le
-- name    : BalanceSpecification.FiveSymbol.wordCount_tail_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:12:04.234288+00:00
-- url     : https://prove2.me/theorems/0f97f0c6-7d50-4df2-918f-4864bfca2c1c
-- title:
--   Five Symbol: word Count tail le
-- statement:
--   The Five Symbol construction uses the word Count tail le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbolBalance.lean#L323-L334
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbolBalance.lean#L323-L334

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

theorem BalanceSpecification.FiveSymbol.wordCount_tail_le {n l : ℕ} (hl : l ≤ n) :
    (wordCount (language shift) (n - l) : ℝ) ≤
      (1 / 4 : ℝ) ^ l * wordCount (language shift) n := by sorry
