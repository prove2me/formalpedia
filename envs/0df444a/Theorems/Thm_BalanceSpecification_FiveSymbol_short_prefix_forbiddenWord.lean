-- Prove2me | Theorems.Thm_BalanceSpecification_FiveSymbol_short_prefix_forbiddenWord
-- name    : BalanceSpecification.FiveSymbol.short_prefix_forbiddenWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:11:38.110862+00:00
-- url     : https://prove2.me/theorems/62e58084-2163-46b6-8e92-952e1f0a738c
-- title:
--   Five Symbol: short prefix forbidden Word
-- statement:
--   A short initial prefix lies in the initial zero and its following run of ones.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbolBalance.lean#L91-L107
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbolBalance.lean#L91-L107

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

theorem BalanceSpecification.FiveSymbol.short_prefix_forbiddenWord {s : Word Alphabet} {j l : ℕ}
    (hs : s <+: forbiddenWord j) (hlen : s.length = l) (hl : 0 < l)
    (hshort : l ≤ markerLength j + 1) :
    s = [0] ++ List.replicate (l - 1) 1 := by sorry
