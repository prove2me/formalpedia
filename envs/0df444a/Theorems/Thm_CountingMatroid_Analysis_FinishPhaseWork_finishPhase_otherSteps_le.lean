-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_FinishPhaseWork_finishPhase_otherSteps_le
-- name    : CountingMatroid.Analysis.FinishPhaseWork.finishPhase_otherSteps_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:48:33.990293+00:00
-- url     : https://prove2.me/theorems/e31f7e7d-471b-4c47-bc4c-ddb0e6bb8e07
-- title:
--   An explicit charged-work bound for phase finishing
-- statement:
--   Let $n\in\mathbb N$, let $s$ be an annealing schedule with observation count $N=s.\mathrm{observations}$ and phase count $L=s.L$, and let $j\in\mathbb N$ be a phase index. Let $w_{ik}\in\mathbb Q$ be multipliers indexed by distinct ordered coordinates $i,k\in[n]$. An observation record contains a paired state, a tape cursor, a natural count $c_\gamma$ for each classifier kind $\gamma$, and a rational numerator sum $u$. Write $c_T$ for its transversal count and $c_{ik}$ for its ordered-defect count. For a rational $a$, define $\operatorname{len}(a)=2+(\operatorname{log2}|\operatorname{num}(a)|+1)+(\operatorname{log2}\operatorname{den}(a)+1)$ using canonical numerator and positive denominator, with $\operatorname{log2}(0)=0$.
--
--   Let $B\in\mathbb N$, assume $c_\gamma\le N$ for every classifier kind, and assume $\operatorname{len}(w_{ik})\le B$ for every multiplier. Put
--
--   $$E=N+4,\qquad F(n,E,b)=3n^2+E+10+4E^2+2(b+4E)^2.$$
--
--   The nonoracle primitive charge $W$ of phase finishing, including executions that abort, satisfies
--
--   $$\begin{aligned}
--   W\le{}&n^2+5+2E+4E^2+2(\operatorname{len}(u)+3E)^2\\
--   &+n^2F(n,E,B+4n^2E+4nE).
--   \end{aligned}$$
--
--   Here $W$ sums the source's charged fair-bit and named nonoracle instruction counters. This is an explicit bound in that abstract accounting model.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/FinishPhaseWork.lean#L43-L232

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
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseWork
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
set_option autoImplicit false
namespace CountingMatroid.Analysis.FinishPhaseWork
end CountingMatroid.Analysis.FinishPhaseWork
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.FinishPhaseWork
open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines CountingMatroid.Program
open CountingMatroid.Analysis.ResourceBound
open CountingMatroid.Analysis.PhaseChainWork
open CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
open CountingMatroid.Analysis.BoundedRunResourceEnvelope

theorem CountingMatroid.Analysis.FinishPhaseWork.finishPhase_otherSteps_le {n : ℕ} (s : AnnealingSchedule) (j B : ℕ)
    (weights : Multipliers n) (observed : ObservationCursor n)
    (hc : ∀ kind, observed.counts kind ≤ s.observations)
    (hw : ∀ i, binaryRatLength (weights i) ≤ B) :
    otherSteps (finishPhase s j weights observed) ≤
      n * n + 5 + 2 * (s.observations + 4) + 4 * (s.observations + 4) ^ 2 +
        2 * (binaryRatLength observed.numeratorSum + 3 * (s.observations + 4)) ^ 2 +
        n * n * finishEntryBudget n (s.observations + 4)
          (B + n * n * (4 * (s.observations + 4)) + n * (4 * (s.observations + 4))) := by sorry
