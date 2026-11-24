-- Prove2me | Theorems.Thm_BalanceSpecification_FiveSymbol_concat_twos_mem_language
-- name    : BalanceSpecification.FiveSymbol.concat_twos_mem_language
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:52:04.234803+00:00
-- url     : https://prove2.me/theorems/5b843c40-fb8d-4977-b7c7-7e2fe56cdc98
-- title:
--   Five Symbol: concat twos mem language
-- statement:
--   Any bridge made of `2`s longer than the left word is admissible. This
--   is the concrete mixing construction in the source.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L288-L362
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L288-L362

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

theorem BalanceSpecification.FiveSymbol.concat_twos_mem_language {u v : Word Alphabet}
    (hu : u ∈ language shift) (hv : v ∈ language shift) {L : ℕ}
    (hL : u.length < L) : u ++ List.replicate L 2 ++ v ∈ language shift := by sorry
