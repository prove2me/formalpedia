-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_BoundedRunOtherSteps_phaseFold_work_and_size
-- name    : CountingMatroid.Analysis.BoundedRunOtherSteps.phaseFold_work_and_size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:37:52.444298+00:00
-- url     : https://prove2.me/theorems/63821fb7-662f-468e-878a-e0661a30602e
-- title:
--   Iterating phases preserves size bounds and adds work budgets
-- statement:
--   Let $n,r\in\mathbb N$, let $o_1,o_2$ be Boolean oracles on subset indicators of an $n$-element set, and fix a tape $t:\mathbb N\to\{0,1\}$. For an annealing schedule $s$, write $L=s.L$, $\tau=s.\tau$, $B=s.\mathrm{restartCap}$, $M=s.\mathrm{observations}$, and $T=s.\mathrm{drawTrials}$ for its phase count, trace-transition count, restart-attempt cap, observation count, and draw-trial cap. Let $\rho=s.\rho$ and define $$S=n+L+\tau+B+M+T+\ell(\rho)+1,$$ where $\ell(a/b)=2+(\lfloor\log_2|a|\rfloor+1)+(\lfloor\log_2 b\rfloor+1)$ for a reduced rational with positive denominator, with $\log_2 0=0$ in this length convention. Assume $\rho\ge0$. For an optional annealing cursor $a$, let $I(S,j,a)$ mean that, whenever $a$ is present, each current multiplier, each stored multiplier at every phase index, and its accumulated product has rational length at most $(j+1)S^{10}$. A cursor contains these weights, the product, and a tape position; an absent cursor denotes an aborted run and satisfies $I$ vacuously. Write $W(A)$ for its charged nonoracle operations, comprising fair-bit reads and named word-operation charges. Let $j,k\in\mathbb N$ satisfy $j+k\le L$, and suppose $I(S,j,a)$ for an initial optional cursor $a$. Let $A$ be the charged fold executing phases $j,j+1,\ldots,j+k-1$ from $a$. Then $$W(A)\le kS^{40},\qquad I(S,j+k,\operatorname{value}(A)).$$ This propagates the rational-size invariant while accumulating the cost of a contiguous block of phases.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/BoundedRunOtherSteps.lean#L29-L59

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

theorem CountingMatroid.Analysis.BoundedRunOtherSteps.phaseFold_work_and_size {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool) (s : AnnealingSchedule)
    (hρ : 0 ≤ s.ρ) (k j : ℕ) (hj : j + k ≤ s.L)
    (acc : Option (AnnealingCursor n))
    (hacc : PhaseSizeInvariant (runSize n s) j acc) :
    let scan := Arlib.Computation.Charged.foldl
      (fun current index => boundedRunPhase r o₁ o₂ tape s index current)
      (List.range' j k) acc
    otherSteps scan ≤ k * (runSize n s) ^ 40 ∧
      PhaseSizeInvariant (runSize n s) (j + k) scan.val := by sorry
