-- Prove2me | Theorems.Thm_BalanceSpecification_FiveSymbol_infix_left_of_end_le
-- name    : BalanceSpecification.FiveSymbol.infix_left_of_end_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:51:44.748287+00:00
-- url     : https://prove2.me/theorems/9adda880-7072-4afa-9f33-a4f7d3ddc392
-- title:
--   Five Symbol: infix left of end le
-- statement:
--   An occurrence ending before a concatenation boundary lies in its left word.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L188-L194
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L188-L194

module
public import Definitions.Def_BalanceSpecificaton_Shortlex
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FiveSymbol
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.FiveSymbol

theorem BalanceSpecification.FiveSymbol.infix_left_of_end_le {f u v p q : Word Alphabet}
    (heq : u ++ v = p ++ f ++ q) (hle : p.length + f.length ≤ u.length) : f <:+: u := by sorry
