-- Prove2me | Theorems.Thm_BalanceSpecification_FiveSymbol_short_suffix_forbiddenWord
-- name    : BalanceSpecification.FiveSymbol.short_suffix_forbiddenWord
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:11:19.406243+00:00
-- url     : https://prove2.me/theorems/e7f33b0c-e5d9-4a06-9732-af45fd71884d
-- title:
--   Five Symbol: short suffix forbidden Word
-- statement:
--   A short terminal suffix lies entirely in the last run of ones and final four.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbolBalance.lean#L58-L73
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbolBalance.lean#L58-L73

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

theorem BalanceSpecification.FiveSymbol.short_suffix_forbiddenWord {s : Word Alphabet} {j l : ℕ}
    (hs : s <:+ forbiddenWord j) (hlen : s.length = l) (hl : 0 < l)
    (hshort : l ≤ markerLength j + 1) :
    s = List.replicate (l - 1) 1 ++ [4] := by sorry
