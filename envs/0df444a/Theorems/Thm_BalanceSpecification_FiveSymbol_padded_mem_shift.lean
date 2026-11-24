-- Prove2me | Theorems.Thm_BalanceSpecification_FiveSymbol_padded_mem_shift
-- name    : BalanceSpecification.FiveSymbol.padded_mem_shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:09:37.396855+00:00
-- url     : https://prove2.me/theorems/cd45c7ff-b25c-46a8-bda5-eefd0aec2107
-- title:
--   Five Symbol: padded mem shift
-- statement:
--   Avoidance of all forbidden subwords makes the explicit padded point valid.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L119-L144
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L119-L144

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

theorem BalanceSpecification.FiveSymbol.padded_mem_shift {w : Word Alphabet}
    (hw : ∀ j : ℕ, 1 ≤ j → ¬ forbiddenWord j <:+: w) :
    padded w ∈ shift.carrier := by sorry
