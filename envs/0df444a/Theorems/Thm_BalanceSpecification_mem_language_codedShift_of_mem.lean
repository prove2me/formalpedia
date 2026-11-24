-- Prove2me | Theorems.Thm_BalanceSpecification_mem_language_codedShift_of_mem
-- name    : BalanceSpecification.mem_language_codedShift_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:56:27.179176+00:00
-- url     : https://prove2.me/theorems/860efd39-be8f-4a74-bc21-300b0e0d4753
-- title:
--   Balance Specification: mem language coded Shift of mem
-- statement:
--   Every generator, including the empty generator when present, occurs in a
--   nonempty coded shift.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/CodedLanguage.lean#L282-L285
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/CodedLanguage.lean#L282-L285

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

theorem BalanceSpecification.mem_language_codedShift_of_mem [TopologicalSpace A]
    {C : Set (Word A)} (hC : ∃ q ∈ C, 0 < q.length)
    {w : Word A} (hw : w ∈ C) : w ∈ language (codedShift C) := by sorry
