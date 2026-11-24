-- Prove2me | Theorems.Thm_BalanceSpecification_exists_entropy_maximizing_invariant_probability
-- name    : BalanceSpecification.exists_entropy_maximizing_invariant_probability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:14:16.445481+00:00
-- url     : https://prove2.me/theorems/04c274fe-6db1-4964-89da-bfb2138312b2
-- title:
--   Balance Specification: exists entropy maximizing invariant probability
-- statement:
--   Entropy attains its supremum among invariant probabilities. Equality with
--   topological entropy requires the separate blocking argument.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyContinuity.lean#L163-L177
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyContinuity.lean#L163-L177

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

theorem BalanceSpecification.exists_entropy_maximizing_invariant_probability (hX : X.carrier.Nonempty) :
    ∃ (μ : ProbabilityMeasure X.carrier) (hInv : IsInvariant μ),
      ∀ (ν : ProbabilityMeasure X.carrier) (hν : IsInvariant ν),
        measureEntropy ν hν ≤ measureEntropy μ hInv := by sorry
