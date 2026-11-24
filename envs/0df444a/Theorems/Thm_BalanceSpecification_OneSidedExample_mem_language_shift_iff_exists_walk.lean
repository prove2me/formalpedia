-- Prove2me | Theorems.Thm_BalanceSpecification_OneSidedExample_mem_language_shift_iff_exists_walk
-- name    : BalanceSpecification.OneSidedExample.mem_language_shift_iff_exists_walk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:44:20.980621+00:00
-- url     : https://prove2.me/theorems/1d522ffb-9e7d-466c-a62b-56a9c26626e0
-- title:
--   One Sided Example: mem language shift iff exists walk
-- statement:
--   The diagram is proved to present exactly the source's coded shift language.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/OneSidedGraphLanguage.lean#L161-L168
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/OneSidedGraphLanguage.lean#L161-L168

module
public import Definitions.Def_BalanceSpecificaton_OneSidedGraph
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_OneSidedGraphLanguage
set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification BalanceSpecification.OneSidedExample

theorem BalanceSpecification.OneSidedExample.mem_language_shift_iff_exists_walk {w : Word Alphabet} :
    w ∈ language shift ↔ ∃ s t, Walk s w t := by sorry
