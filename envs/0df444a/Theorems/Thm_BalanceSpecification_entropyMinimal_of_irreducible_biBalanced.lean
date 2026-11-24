-- Prove2me | Theorems.Thm_BalanceSpecification_entropyMinimal_of_irreducible_biBalanced
-- name    : BalanceSpecification.entropyMinimal_of_irreducible_biBalanced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:15:40.402932+00:00
-- url     : https://prove2.me/theorems/9f5288ef-1610-4a4e-b07f-de3fc736a64a
-- title:
--   Balance Specification: entropy Minimal of irreducible bi Balanced
-- statement:
--   Every irreducible bi-balanced shift is entropy minimal.
--   Source proposition `prop::irreducible_bi-balanced_entropy-minimal`.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MainEquivalence.lean#L24-L27
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MainEquivalence.lean#L24-L27

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

theorem BalanceSpecification.entropyMinimal_of_irreducible_biBalanced (hX : X.carrier.Nonempty)
    (hirr : Irreducible X) (hB : BiBalanced (language X)) : EntropyMinimal X := by sorry
