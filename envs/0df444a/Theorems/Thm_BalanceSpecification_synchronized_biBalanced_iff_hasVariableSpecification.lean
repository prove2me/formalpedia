-- Prove2me | Theorems.Thm_BalanceSpecification_synchronized_biBalanced_iff_hasVariableSpecification
-- name    : BalanceSpecification.synchronized_biBalanced_iff_hasVariableSpecification
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:52:30.73637+00:00
-- url     : https://prove2.me/theorems/f72e64e0-f1cb-4f0d-a34b-818946f95747
-- title:
--   Balance Specification: synchronized bi Balanced iff has Variable Specification
-- statement:
--   The main theorem: synchronization and bi-balancedness are equivalent to
--   variable specification. All measure-existence, ergodicity, entropy-minimality,
--   and uniform-occurrence obligations are proved in the imported providers.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MainEquivalence.lean#L32-L41
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MainEquivalence.lean#L32-L41

module
public import Definitions.Def_BalanceSpecificaton_GibbsExistence
public import Definitions.Def_BalanceSpecificaton_GibbsErgodic
public import Definitions.Def_BalanceSpecificaton_GibbsEntropyMinimal
public import Definitions.Def_BalanceSpecificaton_Specification
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Definitions.Def_BalanceSpecificaton_MainEquivalence
set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
open MeasureTheory
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}

theorem BalanceSpecification.synchronized_biBalanced_iff_hasVariableSpecification (hX : X.carrier.Nonempty)
    (hirr : Irreducible X) :
    (Synchronized X ∧ BiBalanced (language X)) ↔ HasVariableSpecification X := by sorry
