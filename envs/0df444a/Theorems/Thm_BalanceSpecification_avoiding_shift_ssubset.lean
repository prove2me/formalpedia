-- Prove2me | Theorems.Thm_BalanceSpecification_avoiding_shift_ssubset
-- name    : BalanceSpecification.avoiding_shift_ssubset
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:09:11.724712+00:00
-- url     : https://prove2.me/theorems/e1e6b742-ce21-4d6b-95b3-a92736f966f6
-- title:
--   Balance Specification: avoiding shift ssubset
-- statement:
--   Forbidding an admissible word produces a proper subshift.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyMinimal.lean#L57-L74
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyMinimal.lean#L57-L74

module
public import Definitions.Def_BalanceSpecificaton_FactorialEntropy
public import Definitions.Def_BalanceSpecificaton_Occurrence
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_EntropyMinimal
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open Filter
open scoped Topology
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
omit [Fintype A]

theorem BalanceSpecification.avoiding_shift_ssubset {X : ShiftSpace A} {v : Word A}
    (hv : v ∈ language X) :
    (languageShift (avoidingLanguage (language X) v)).carrier ⊂ X.carrier := by sorry
