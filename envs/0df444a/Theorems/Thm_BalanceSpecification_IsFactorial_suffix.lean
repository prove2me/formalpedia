-- Prove2me | Theorems.Thm_BalanceSpecification_IsFactorial_suffix
-- name    : BalanceSpecification.IsFactorial.suffix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:33:18.576426+00:00
-- url     : https://prove2.me/theorems/9b722d63-5e3f-47e6-ad43-e5cbf6681d8c
-- title:
--   Is Factorial: suffix
-- statement:
--   The Is Factorial construction uses the suffix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Synchronization.lean#L28-L31
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Synchronization.lean#L28-L31

module
public import Definitions.Def_BalanceSpecificaton_Language
public import Definitions.Def_BalanceSpecificaton_Counting
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Synchronization
set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*} {L : Set (Word A)}

theorem BalanceSpecification.IsFactorial.suffix (hL : IsFactorial L) {u v : Word A}
    (h : u ++ v ∈ L) : v ∈ L := by sorry
