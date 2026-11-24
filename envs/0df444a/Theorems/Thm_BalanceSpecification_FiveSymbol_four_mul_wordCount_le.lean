-- Prove2me | Theorems.Thm_BalanceSpecification_FiveSymbol_four_mul_wordCount_le
-- name    : BalanceSpecification.FiveSymbol.four_mul_wordCount_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:11:43.276406+00:00
-- url     : https://prove2.me/theorems/49661b5b-60da-4846-83d1-500628d93a0e
-- title:
--   Five Symbol: four mul word Count le
-- statement:
--   Four independent right extensions force a factor-four complexity increase.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbolBalance.lean#L222-L242
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbolBalance.lean#L222-L242

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

theorem BalanceSpecification.FiveSymbol.four_mul_wordCount_le (n : ℕ) :
    4 * wordCount (language shift) n ≤ wordCount (language shift) (n + 1) := by sorry
