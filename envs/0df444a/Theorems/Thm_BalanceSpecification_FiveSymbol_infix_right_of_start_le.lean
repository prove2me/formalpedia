-- Prove2me | Theorems.Thm_BalanceSpecification_FiveSymbol_infix_right_of_start_le
-- name    : BalanceSpecification.FiveSymbol.infix_right_of_start_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:51:52.764124+00:00
-- url     : https://prove2.me/theorems/6a11adbf-d81d-48f6-ae7b-4373420ec0da
-- title:
--   Five Symbol: infix right of start le
-- statement:
--   An occurrence starting after a concatenation boundary lies in its right word.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L197-L208
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L197-L208

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

theorem BalanceSpecification.FiveSymbol.infix_right_of_start_le {f u v p q : Word Alphabet}
    (heq : u ++ v = p ++ f ++ q) (hle : u.length ≤ p.length) : f <:+: v := by sorry
