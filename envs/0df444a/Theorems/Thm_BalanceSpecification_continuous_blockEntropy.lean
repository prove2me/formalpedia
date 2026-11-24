-- Prove2me | Theorems.Thm_BalanceSpecification_continuous_blockEntropy
-- name    : BalanceSpecification.continuous_blockEntropy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:11:17.827904+00:00
-- url     : https://prove2.me/theorems/38e27bd1-2e69-4d80-a1cc-c4508e84798f
-- title:
--   Balance Specification: continuous block Entropy
-- statement:
--   Every finite block entropy is continuous in the weak topology.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyContinuity.lean#L81-L87
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyContinuity.lean#L81-L87

module
public import Definitions.Def_BalanceSpecificaton_MaximalEntropy
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_EntropyContinuity
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open MeasureTheory Filter Set
open scoped Topology
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}

theorem BalanceSpecification.continuous_blockEntropy (X : ShiftSpace A) (n : ℕ) :
    Continuous (fun μ : ProbabilityMeasure X.carrier => blockEntropy μ n) := by sorry
