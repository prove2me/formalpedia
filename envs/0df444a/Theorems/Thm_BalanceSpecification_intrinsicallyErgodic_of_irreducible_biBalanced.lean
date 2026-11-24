-- Prove2me | Theorems.Thm_BalanceSpecification_intrinsicallyErgodic_of_irreducible_biBalanced
-- name    : BalanceSpecification.intrinsicallyErgodic_of_irreducible_biBalanced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:16:12.597381+00:00
-- url     : https://prove2.me/theorems/a6562050-1b35-45c0-bbd8-96a3a24ca392
-- title:
--   Balance Specification: intrinsically Ergodic of irreducible bi Balanced
-- statement:
--   The second main theorem: every irreducible bi-balanced shift admits
--   exactly one invariant measure of maximal entropy.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/IntrinsicErgodicity.lean#L54-L57
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/IntrinsicErgodicity.lean#L54-L57

module
public import Definitions.Def_BalanceSpecificaton_MaximalEntropy
public import Definitions.Def_BalanceSpecificaton_AbsoluteContinuity
public import Definitions.Def_BalanceSpecificaton_GibbsErgodic
public import Mathlib.Dynamics.Ergodic.Extreme
public import Definitions.Def_BalanceSpecificaton_IntrinsicErgodicity
set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
open MeasureTheory
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}

theorem BalanceSpecification.intrinsicallyErgodic_of_irreducible_biBalanced (hX : X.carrier.Nonempty)
    (hirr : Irreducible X) (hB : BiBalanced (language X)) : IntrinsicallyErgodic X hX := by sorry
