-- Prove2me | Theorems.Thm_BalanceSpecification_FiveSymbol_mem_language_iff_avoids
-- name    : BalanceSpecification.FiveSymbol.mem_language_iff_avoids
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:51:09.675284+00:00
-- url     : https://prove2.me/theorems/346f38d4-759b-4238-9bda-3d9452ab8c1c
-- title:
--   Five Symbol: mem language iff avoids
-- statement:
--   The finite forbidden-word test is exact for this specific example, because
--   every avoiding word has the explicit two-sided extension above.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L148-L154
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L148-L154

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

theorem BalanceSpecification.FiveSymbol.mem_language_iff_avoids (w : Word Alphabet) :
    w ∈ language shift ↔ ∀ j : ℕ, 1 ≤ j → ¬ forbiddenWord j <:+: w := by sorry
