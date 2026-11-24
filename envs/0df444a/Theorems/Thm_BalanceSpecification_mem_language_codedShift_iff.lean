-- Prove2me | Theorems.Thm_BalanceSpecification_mem_language_codedShift_iff
-- name    : BalanceSpecification.mem_language_codedShift_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:36:43.818013+00:00
-- url     : https://prove2.me/theorems/53c70e72-b79a-4a01-9fdc-de17404777a6
-- title:
--   Balance Specification: mem language coded Shift iff
-- statement:
--   The full language characterization uses actual finite generator
--   concatenations; it does not redefine the coded shift by its intended language.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/CodedLanguage.lean#L254-L260
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/CodedLanguage.lean#L254-L260

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

theorem BalanceSpecification.mem_language_codedShift_iff [TopologicalSpace A] [DiscreteTopology A]
    {C : Set (Word A)} (hC : ∃ q ∈ C, 0 < q.length) {w : Word A} :
    w ∈ language (codedShift C) ↔ ∃ v ∈ generatedWords C, w <:+: v := by sorry
