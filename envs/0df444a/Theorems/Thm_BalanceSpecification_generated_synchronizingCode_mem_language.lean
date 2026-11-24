-- Prove2me | Theorems.Thm_BalanceSpecification_generated_synchronizingCode_mem_language
-- name    : BalanceSpecification.generated_synchronizingCode_mem_language
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:16:05.437644+00:00
-- url     : https://prove2.me/theorems/5aa5d4a9-5288-4dd5-8706-df51f497cc83
-- title:
--   Balance Specification: generated synchronizing Code mem language
-- statement:
--   Prefixing any finite concatenation of return words preserves admissibility
--   through the synchronizing word.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SynchronizedCoded.lean#L24-L44
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SynchronizedCoded.lean#L24-L44

module
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SynchronizedCoded
set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] {X : ShiftSpace A}
omit [DiscreteTopology A]

theorem BalanceSpecification.generated_synchronizingCode_mem_language {v : Word A}
    (hv : IsSynchronizing (language X) v) :
    generatedWords (synchronizingCode X v) ⊆ language X := by sorry
