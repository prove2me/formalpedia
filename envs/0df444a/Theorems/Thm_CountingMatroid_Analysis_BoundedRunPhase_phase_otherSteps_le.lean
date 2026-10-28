-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_BoundedRunPhase_phase_otherSteps_le
-- name    : CountingMatroid.Analysis.BoundedRunPhase.phase_otherSteps_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:34:52.899993+00:00
-- url     : https://prove2.me/theorems/6c5022e6-80c4-4d5a-b954-2078335fe2ff
-- title:
--   One bounded phase has at most $S^{40}$ nonoracle charges
-- statement:
--   Let $n,r\in\mathbb N$, let $o_1,o_2$ be Boolean oracles on subset indicators of an $n$-element set, and fix a tape $t:\mathbb N\to\{0,1\}$. For an annealing schedule $s$, write $L=s.L$, $\tau=s.\tau$, $B=s.\mathrm{restartCap}$, $M=s.\mathrm{observations}$, and $T=s.\mathrm{drawTrials}$ for its phase count, trace-transition count, restart-attempt cap, observation count, and draw-trial cap. Let $\rho=s.\rho$ and define $$S=n+L+\tau+B+M+T+\ell(\rho)+1,$$ where $\ell(a/b)=2+(\lfloor\log_2|a|\rfloor+1)+(\lfloor\log_2 b\rfloor+1)$ for a reduced rational with positive denominator, with $\log_2 0=0$ in this length convention. Assume $\rho\ge0$. For an optional annealing cursor $a$, let $I(S,j,a)$ mean that, whenever $a$ is present, each current multiplier, each stored multiplier at every phase index, and its accumulated product has rational length at most $(j+1)S^{10}$. A cursor contains these weights, the product, and a tape position; an absent cursor denotes an aborted run and satisfies $I$ vacuously. Write $W(A)$ for its charged nonoracle operations, comprising fair-bit reads and named word-operation charges. For any $j<L$ and initial optional cursor $a$ satisfying $I(S,j,a)$, $$W(\operatorname{phase}_j(a))\le S^{40}.$$ The phase body computes its parameter, restarts, observes, finishes, multiplies the ratio, and conditionally writes learned weights. This estimate includes work already spent on paths that later abort.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/BoundedRunPhaseWork.lean#L98-L265

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
/-!
The full nonoracle-work bound for one bounded annealing phase follows from
proved capped-chain, restart, observation, and finishing cost bounds. Each
bound includes abort paths; the observation and finishing scans carry their
reached rational-size invariants. The explicit sum of these component budgets
is absorbed into `runSize ^ 40`, with the original theorem statement retained.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace CountingMatroid.Analysis.BoundedRunPhase
end CountingMatroid.Analysis.BoundedRunPhase
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.BoundedRunPhase
open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines CountingMatroid.Program

open CountingMatroid.Analysis.ResourceBound
open CountingMatroid.Analysis.BoundedRunResourceEnvelope
open CountingMatroid.Analysis.PhaseChainWork
open CountingMatroid.Analysis.RestartPhaseWork
open CountingMatroid.Analysis.ObservePhaseWork
open CountingMatroid.Analysis.FinishPhaseWork
open CountingMatroid.Analysis.RationalHeight

theorem CountingMatroid.Analysis.BoundedRunPhase.phase_otherSteps_le {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (hρ : 0 ≤ s.ρ)
    (j : ℕ) (hj : j < s.L) (acc : Option (AnnealingCursor n))
    (hacc : PhaseSizeInvariant (runSize n s) j acc) :
    otherSteps (boundedRunPhase r o₁ o₂ tape s j acc) ≤ (runSize n s) ^ 40 := by sorry
