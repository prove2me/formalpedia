-- Prove2me | Theorems.Thm_BalanceSpecification_IsGibbsMeasure_eq_of_maximalEntropy
-- name    : BalanceSpecification.IsGibbsMeasure.eq_of_maximalEntropy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:12:25.821622+00:00
-- url     : https://prove2.me/theorems/a46fe7e9-7ffd-425b-86eb-2077caec9050
-- title:
--   Is Gibbs Measure: eq of maximal Entropy
-- statement:
--   Every maximal-entropy measure equals an ergodic Gibbs measure on an
--   irreducible shift. Absolute continuity is proved from finite block bounds.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/IntrinsicErgodicity.lean#L40-L50
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/IntrinsicErgodicity.lean#L40-L50

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

theorem BalanceSpecification.IsGibbsMeasure.eq_of_maximalEntropy {hX : X.carrier.Nonempty}
    {μ ν : ProbabilityMeasure X.carrier} (hG : IsGibbsMeasure hX μ)
    (hirr : Irreducible X) (hν : IsMaximalEntropyMeasure hX ν) : ν = μ := by sorry
