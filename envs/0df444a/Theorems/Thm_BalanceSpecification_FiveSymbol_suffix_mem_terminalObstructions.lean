-- Prove2me | Theorems.Thm_BalanceSpecification_FiveSymbol_suffix_mem_terminalObstructions
-- name    : BalanceSpecification.FiveSymbol.suffix_mem_terminalObstructions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:11:30.221342+00:00
-- url     : https://prove2.me/theorems/44adccf0-e0b7-4a05-bac6-095d472b8f2a
-- title:
--   Five Symbol: suffix mem terminal Obstructions
-- statement:
--   Every positive-length forbidden suffix is in the explicit bounded candidate set.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbolBalance.lean#L76-L88
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbolBalance.lean#L76-L88

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

theorem BalanceSpecification.FiveSymbol.suffix_mem_terminalObstructions {s : Word Alphabet} {j l : ℕ}
    (hs : s <:+ forbiddenWord j) (hlen : s.length = l) (hl : 0 < l) :
    s ∈ terminalObstructions l := by sorry
