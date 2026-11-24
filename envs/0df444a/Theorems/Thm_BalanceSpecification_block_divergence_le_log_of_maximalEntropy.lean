-- Prove2me | Theorems.Thm_BalanceSpecification_block_divergence_le_log_of_maximalEntropy
-- name    : BalanceSpecification.block_divergence_le_log_of_maximalEntropy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:12:12.836261+00:00
-- url     : https://prove2.me/theorems/7e4c2f5a-6113-4722-9954-49e71714e739
-- title:
--   Balance Specification: block divergence le log of maximal Entropy
-- statement:
--   The finite-block divergence estimate from the intrinsic-ergodicity proof.
--   Maximal entropy supplies the block entropy lower bound rather than assuming it.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/IntrinsicErgodicity.lean#L23-L36
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/IntrinsicErgodicity.lean#L23-L36

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

theorem BalanceSpecification.block_divergence_le_log_of_maximalEntropy {hX : X.carrier.Nonempty}
    {μ ν : ProbabilityMeasure X.carrier} {K : ℝ} (hB : GibbsBounds hX μ K)
    (hν : IsMaximalEntropyMeasure hX ν) (n : ℕ) :
    FiniteEntropy.divergence (blockDistribution ν n) (blockDistribution μ n) ≤ Real.log K := by sorry
