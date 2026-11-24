-- Prove2me | Theorems.Thm_BalanceSpecification_FiveSymbol_prepend_mem_language
-- name    : BalanceSpecification.FiveSymbol.prepend_mem_language
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:44:28.924895+00:00
-- url     : https://prove2.me/theorems/3db80eef-f30e-4964-bfed-9d25cff4a736
-- title:
--   Five Symbol: prepend mem language
-- statement:
--   Every symbol other than the initial marker `0` may be freely prepended.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L178-L185
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L178-L185

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

theorem BalanceSpecification.FiveSymbol.prepend_mem_language {w : Word Alphabet} (hw : w ∈ language shift)
    {a : Alphabet} (ha : a ≠ 0) : a :: w ∈ language shift := by sorry
