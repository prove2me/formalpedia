-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_PhaseBitCursorBound_traceReturn_preserves_bit_budget
-- name    : CountingMatroid.Analysis.PhaseBitCursorBound.traceReturn_preserves_bit_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:58:26.551988+00:00
-- url     : https://prove2.me/theorems/bc7c93dd-d9c9-4f08-8761-0ed822a9563c
-- title:
--   A trace return preserves the shared tape budget
-- statement:
--   Let $G=[n]\times\{0,1\}$ be the paired ground set, with Boolean labels written as $0,1$. A state is a subset of $G$. Fix $r\in\mathbb N$, arbitrary Boolean oracles $o_1,o_2$, a tape $\mathbb N\to\{0,1\}$, and an annealing schedule $s$. For a rational $x$, let $\ell(x)=2+(\lfloor\log_2|\operatorname{num}(x)|\rfloor+1)+(\lfloor\log_2\operatorname{den}(x)\rfloor+1)$ be its canonical rational encoding length, with $\log_2 0=0$; thus $\ell(1)=4$. Write $T=s.\mathrm{drawTrials}$ and $A=s.\mathrm{restartCap}$. Let $q\in\mathbb Q$, let $w$ assign rational multipliers to every ordered distinct empty/full pair index, and let $b,K\in\mathbb N$. Put $$C=1+3T(4K+n+1).$$ A restart cursor stores a paired state, a natural tape cursor, and a natural attempt count. Let $a_{\rm in},c_{\rm in}$ and $a_{\rm out},c_{\rm out}$ denote these counters in initial and output cursors. Assume $$\ell(1)+n\ell(q)\le K,\quad\forall i,\ \ell(w(i))\le K,\quad a_{\rm in}\le A,\quad c_{\rm in}\le b+a_{\rm in}C.$$ If the trace-return procedure succeeds with the given output cursor, then $$a_{\rm out}\le A,\qquad c_{\rm out}\le b+a_{\rm out}C.$$
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/PhaseBitCursorBound.lean#L32-L121

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
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseHistory
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformReplay
import Definitions.Def_CountingMatroid_Analysis_ChainDrawSiteReplay
import Definitions.Def_CountingMatroid_Analysis_ChainStepIntervalReplay
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
import Definitions.Def_CountingMatroid_Analysis_TransversalPartition
import Definitions.Def_CountingMatroid_Analysis_TransversalProjection
import Definitions.Def_CountingMatroid_Interface_Pseudocode
import Definitions.Def_CountingMatroid_Interface_Pseudocode_Extension1
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
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.List
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

namespace CountingMatroid.Analysis.PhaseBitCursorBound
end CountingMatroid.Analysis.PhaseBitCursorBound
namespace CountingMatroid.Analysis.InitialRestartLaw
end CountingMatroid.Analysis.InitialRestartLaw
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
namespace CountingMatroid.Analysis.PhaseHistoryMultiplierLength
end CountingMatroid.Analysis.PhaseHistoryMultiplierLength
namespace CountingMatroid.Analysis.FinishPhaseWeightsSize
end CountingMatroid.Analysis.FinishPhaseWeightsSize
namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
namespace CountingMatroid.Analysis.LeastHalvingsCost
end CountingMatroid.Analysis.LeastHalvingsCost
namespace CountingMatroid.Analysis
end CountingMatroid.Analysis
namespace CountingMatroid.Analysis.ChainStepBitBound
end CountingMatroid.Analysis.ChainStepBitBound
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CountingMatroid.Analysis.PhaseBitCursorBound
end CountingMatroid.Analysis.PhaseBitCursorBound
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.PhaseBitCursorBound

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.ChainStepBitBound
open CountingMatroid.Analysis.BoundedRunResourceEnvelope

theorem CountingMatroid.Analysis.PhaseBitCursorBound.traceReturn_preserves_bit_budget {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (q : ℚ) (weights : Multipliers n)
    (base K : ℕ) (start out : RestartCursor n)
    (hq : binaryRatLength 1 + n * binaryRatLength q ≤ K)
    (hw : ∀ i, binaryRatLength (weights i) ≤ K)
    (ha : start.attempts ≤ s.restartCap)
    (hb : start.bitCursor ≤ base + start.attempts * (1 + 3 * s.drawTrials * (4 * K + n + 1)))
    (h : (traceReturn r o₁ o₂ tape s q weights start).val = some out) :
    out.attempts ≤ s.restartCap ∧
    out.bitCursor ≤ base + out.attempts * (1 + 3 * s.drawTrials * (4 * K + n + 1)) := by sorry
