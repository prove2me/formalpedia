-- Prove2me | Theorems.Thm_BalanceSpecification_mem_language_codedShift_of_mem_generatedWords
-- name    : BalanceSpecification.mem_language_codedShift_of_mem_generatedWords
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:36:36.059012+00:00
-- url     : https://prove2.me/theorems/bc99f454-3e03-4d80-934e-f03e9a6612a3
-- title:
--   Balance Specification: mem language coded Shift of mem generated Words
-- statement:
--   Finite concatenations of generators belong to the literal coded shift.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/CodedLanguage.lean#L246-L250
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/CodedLanguage.lean#L246-L250

module
public import Definitions.Def_BalanceSpecificaton_Coded
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*}

theorem BalanceSpecification.mem_language_codedShift_of_mem_generatedWords [TopologicalSpace A]
    {C : Set (Word A)} (hC : ∃ q ∈ C, 0 < q.length)
    {v : Word A} (hv : v ∈ generatedWords C) : v ∈ language (codedShift C) := by sorry
