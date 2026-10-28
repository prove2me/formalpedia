-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_BoundedRunOtherSteps_finalization_otherSteps_le
-- name    : CountingMatroid.Analysis.BoundedRunOtherSteps.finalization_otherSteps_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:46:59.394377+00:00
-- url     : https://prove2.me/theorems/162e12d5-1fa3-4dd8-a1d9-5879d6099067
-- title:
--   Final scaling has polynomial charged work in the product length
-- statement:
--   Let $n,K\in\mathbb N$ and let $a$ be an optional annealing cursor, containing learned weights, current weights, a rational product $P$, and a tape position $c$ when present. Assume that every present cursor selected by $a$ has rational encoding length $\ell(P)\le K$, where $\ell$ counts a sign bit, a delimiter, and the binary lengths of the reduced numerator magnitude and positive denominator, with one digit for zero. Let $F(a)$ return $(0,0)$ when $a$ is absent and otherwise compute $2^n$, convert it to a rational, and return $(2^nP,c)$. Write $W(A)$ for its charged nonoracle operations, comprising fair-bit reads and named word-operation charges. Then $$W(F(a))\le3n+1+(2n+4+K)^2.$$ This controls the final estimate computation by logarithmic operand size.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/BoundedRunOtherSteps.lean#L61-L115

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Cost_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Dict
import Definitions.Def_CountingMatroidSupport_Computation_Heap
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Machine_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Num
import Definitions.Def_CountingMatroidSupport_Computation_Queue
import Definitions.Def_CountingMatroidSupport_Computation_Rand
import Definitions.Def_CountingMatroidSupport_Computation_Roster
import Definitions.Def_CountingMatroidSupport_Computation_Slot
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroidSupport_Computation_Std
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhase
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseWork
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseWork
import Definitions.Def_CountingMatroid_Analysis_ObservePhaseWork
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Program
import Definitions.Def_CountingMatroid_Model_Run
import Definitions.Def_CountingMatroid_Model_Subroutines
import Lean
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF

namespace CountingMatroid.Analysis.BoundedRunOtherSteps
end CountingMatroid.Analysis.BoundedRunOtherSteps
namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
namespace CountingMatroid.Analysis.LeastHalvingsCost
end CountingMatroid.Analysis.LeastHalvingsCost
namespace CountingMatroid.Analysis
end CountingMatroid.Analysis
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.RestartPhaseWork
end CountingMatroid.Analysis.RestartPhaseWork
namespace CountingMatroid.Analysis.BoundedRunPhase
end CountingMatroid.Analysis.BoundedRunPhase
namespace CountingMatroid.Analysis.FinishPhaseWeightsSize
end CountingMatroid.Analysis.FinishPhaseWeightsSize
set_option autoImplicit false

/-!
The bounded-run nonoracle-work envelope is reduced to two single-phase
obligations: `phase_preserves_size` and `phase_otherSteps_le`. Their files
record the remaining multiplier-size and abort-path work proofs.

This module combines those statements by induction over the actual indexed
phase loop, bounds initialization, and proves the final-scaling work bound.
The full envelope is conditional on those two open child obligations; it is
not yet a completed resource proof. Existing power/count/height support is
still downstream in `BoundedRunResourceEnvelope` and needs upstream extraction
for use in the child proofs.
-/

namespace CountingMatroid.Analysis.BoundedRunOtherSteps
end CountingMatroid.Analysis.BoundedRunOtherSteps
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.BoundedRunOtherSteps
open CountingMatroid.Model
open CountingMatroid.Model.Subroutines

open CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.BoundedRunPhase
open CountingMatroid.Analysis.ResourceBound

theorem CountingMatroid.Analysis.BoundedRunOtherSteps.finalization_otherSteps_le {n : ℕ}
    (result : Option (AnnealingCursor n)) (K : ℕ)
    (hresult : ∀ current, result = some current → binaryRatLength current.product ≤ K) :
    otherSteps (match result with
      | none => pure ((0 : ℚ), (0 : ℕ))
      | some current => do
          let powerOfTwo ← natPower 2 n
          let scale ← ratOfNat powerOfTwo
          let estimate ← ratMul scale current.product
          pure (estimate, current.bitCursor)) ≤
      3 * n + 1 + (2 * n + 4 + K) ^ 2 := by sorry
