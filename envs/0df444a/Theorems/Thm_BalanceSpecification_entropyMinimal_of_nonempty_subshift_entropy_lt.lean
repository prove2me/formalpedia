-- Prove2me | Theorems.Thm_BalanceSpecification_entropyMinimal_of_nonempty_subshift_entropy_lt
-- name    : BalanceSpecification.entropyMinimal_of_nonempty_subshift_entropy_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:09:17.001129+00:00
-- url     : https://prove2.me/theorems/5fc5b9dc-97ab-49cf-af34-203e9d394bc2
-- title:
--   Balance Specification: entropy Minimal of nonempty subshift entropy lt
-- statement:
--   Real entropy inequalities for nonempty proper subshifts imply the complete
--   extended-entropy definition, including the empty subshift.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyMinimal.lean#L43-L53
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyMinimal.lean#L43-L53

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
omit [DiscreteTopology A]

theorem BalanceSpecification.entropyMinimal_of_nonempty_subshift_entropy_lt {X : ShiftSpace A}
    (hX : X.carrier.Nonempty)
    (hless : ∀ (Y : ShiftSpace A) (hY : Y.carrier.Nonempty),
      Y.carrier ⊂ X.carrier → entropy Y hY < entropy X hX) : EntropyMinimal X := by sorry
