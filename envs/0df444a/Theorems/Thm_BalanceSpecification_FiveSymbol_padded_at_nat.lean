-- Prove2me | Theorems.Thm_BalanceSpecification_FiveSymbol_padded_at_nat
-- name    : BalanceSpecification.FiveSymbol.padded_at_nat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:51:43.314464+00:00
-- url     : https://prove2.me/theorems/7b49cceb-62b7-4e8b-9e1c-f7fce4c48e63
-- title:
--   Five Symbol: padded at nat
-- statement:
--   The Five Symbol construction uses the padded at nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L85-L88
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L85-L88

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

theorem BalanceSpecification.FiveSymbol.padded_at_nat (w : Word Alphabet) {i : ℕ} (hi : i < w.length) :
    padded w (i : ℤ) = w[i] := by sorry
