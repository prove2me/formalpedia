-- Prove2me | Theorems.Thm_BalanceSpecification_FiveSymbol_append_mem_language
-- name    : BalanceSpecification.FiveSymbol.append_mem_language
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:09:58.684216+00:00
-- url     : https://prove2.me/theorems/9922c33b-355c-436b-a7c5-6b0ad78217c0
-- title:
--   Five Symbol: append mem language
-- statement:
--   Every symbol other than the terminal marker `4` may be freely appended.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L168-L175
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L168-L175

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

theorem BalanceSpecification.FiveSymbol.append_mem_language {w : Word Alphabet} (hw : w ∈ language shift)
    {a : Alphabet} (ha : a ≠ 4) : w ++ [a] ∈ language shift := by sorry
