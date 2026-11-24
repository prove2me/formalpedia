-- Prove2me | Theorems.Thm_BalanceSpecification_blockEntropy_finiteOrbitProbability_ge
-- name    : BalanceSpecification.blockEntropy_finiteOrbitProbability_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:12:55.727245+00:00
-- url     : https://prove2.me/theorems/93d07577-9a1b-4583-9520-0f7fd9ee770b
-- title:
--   Balance Specification: block Entropy finite Orbit Probability ge
-- statement:
--   Concavity bounds the entropy of a finite orbit average from below by the
--   average entropies of its shifted initial measures.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/VariationalPrinciple.lean#L107-L126
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/VariationalPrinciple.lean#L107-L126

module
public import Definitions.Def_BalanceSpecificaton_EntropyContinuity
public import Definitions.Def_BalanceSpecificaton_TilingBounds
public import Definitions.Def_BalanceSpecificaton_BlockingEstimate
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_VariationalPrinciple
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open MeasureTheory Filter Set
open scoped Topology
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}

theorem BalanceSpecification.blockEntropy_finiteOrbitProbability_ge {I : Type*} [Fintype I] [Nonempty I]
    (x : I → X.carrier) (N n : ℕ) :
    ((N + 1 : ℕ) : ℝ)⁻¹ * ∑ j : Fin (N + 1),
      blockEntropy (translatedProbability (finitePointProbability x) j.val) n ≤
      blockEntropy (finiteOrbitProbability (shiftMap X) x N) n := by sorry
