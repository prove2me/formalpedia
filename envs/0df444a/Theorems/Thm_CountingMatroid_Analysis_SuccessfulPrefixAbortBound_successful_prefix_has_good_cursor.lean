-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_SuccessfulPrefixAbortBound_successful_prefix_has_good_cursor
-- name    : CountingMatroid.Analysis.SuccessfulPrefixAbortBound.successful_prefix_has_good_cursor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:00:36.861383+00:00
-- url     : https://prove2.me/theorems/cbf336df-1c28-4086-b86a-7066cefae11a
-- title:
--   A successful finite prefix has a good cursor and exact truncated length
-- statement:
--   Let $n,r\in\mathbb N$, let $o_1,o_2$ be arbitrary Boolean independence-query functions on subsets of $[n]$, and let $p=(\varepsilon,\delta)\in\mathbb Q^2$ satisfy $0<\varepsilon,\delta<1$. Let $s=\operatorname{setup}(n,p)$ have annealing factor $\rho$, phase count $L$, and local tolerance $\eta$. For a subset $A\subseteq[n]$, let $T(A)$ select label $0$ on $A$ and label $1$ elsewhere; for a paired state $S$, put $d(S)=n-\operatorname{pairedRank}(r,o_1,o_2,S)$ with truncated natural subtraction. Define
--   $$C_a=\sum_{A\subseteq[n]}(\rho^a)^{d(T(A))},\qquad D_{a,ik}=\sum_{S\text{ of defect }(i,k)}(\rho^a)^{d(S)},\qquad I_{a,ik}=C_a/D_{a,ik}.$$
--   Here a defect $(i,k)$ has empty pair $i$, full pair $k$, and one label at every other pair, with $i\ne k$. A cursor is good at phase $j$ when every stored table entry at level $a\le j$ lies between $I_{a,ik}/4$ and $4I_{a,ik}$, and its current multipliers satisfy the same bounds at level $j$. Write $H_j(t)$ for the optional initialized history on tape $t$ after $j$ phases. A certificate for phase $a$ asserts successful cursors $v,v'$ with $H_a(t)=v$ and bounded phase $a$ returning $v'$, goodness of $v$ at $a$, and goodness of $v'$ at $a+1$ whenever $a+1<L$. It also supplies a rational ratio $R$ with
--   $$\frac{1-\eta}{1+\eta}\le\frac{R}{C_{a+1}/C_a}\le\frac{1+\eta}{1-\eta},\qquad v'.\mathrm{product}=v.\mathrm{product}\,R.$$
--   Let $j<L$ and let $m=\operatorname{blockLength}(n,r,p)$ be the prescribed finite run budget. For a Boolean list $b$ of length $m$, define its defaulted tape by $t_b(i)=b_i$ when $i<m$ and $t_b(i)=0$ otherwise. Call a list $h$ a successful phase prefix if some such $b$ certifies every phase $a<j$ and $h$ is the initial segment of $b$ of length given by the history cursor at $j$, using length zero if the history has failed. If $h$ is a successful phase prefix, then there exist a length-$m$ list $b$ and a cursor $v$ such that all earlier phase certificates hold on $t_b$, $H_j(t_b)=v$, $v$ is good at $j$, and
--   $$h=\operatorname{take}_{c(v)}(b),\qquad |h|=\min\{c(v),m\},$$
--   where $c(v)$ is the cursor’s tape position.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/SuccessfulPrefixCursor.lean#L41-L71

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
import Definitions.Def_CountingMatroid_Analysis_AnnealingPartitionDrift
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhase
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseHistory
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseWork
import Definitions.Def_CountingMatroid_Analysis_DefectPartitionPositive
import Definitions.Def_CountingMatroid_Analysis_EmpiricalPhaseCertificate
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseEmpiricalUpdate
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseWork
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_InitialMultipliersGood
import Definitions.Def_CountingMatroid_Analysis_ObservePhaseWork
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseMeanCertificate
import Definitions.Def_CountingMatroid_Analysis_PhaseObservationExperiment
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
import Definitions.Def_CountingMatroid_Analysis_StationaryMeanIdentities
import Definitions.Def_CountingMatroid_Analysis_TransversalClassPartition
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
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.List
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF

namespace CountingMatroid.Analysis.SuccessfulPrefixAbortBound
end CountingMatroid.Analysis.SuccessfulPrefixAbortBound
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
namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope
end CountingMatroid.Analysis.BoundedRunResourceEnvelope
namespace CountingMatroid.Analysis.BoundedRunOtherSteps
end CountingMatroid.Analysis.BoundedRunOtherSteps
namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
namespace CountingMatroid.Analysis.LeastHalvingsCost
end CountingMatroid.Analysis.LeastHalvingsCost
namespace CountingMatroid.Analysis
end CountingMatroid.Analysis
namespace CountingMatroid.Analysis.RestartPhaseWork
end CountingMatroid.Analysis.RestartPhaseWork
namespace CountingMatroid.Analysis.BoundedRunPhase
end CountingMatroid.Analysis.BoundedRunPhase
namespace CountingMatroid.Analysis.FinishPhaseWeightsSize
end CountingMatroid.Analysis.FinishPhaseWeightsSize
namespace CountingMatroid.Analysis.BoundedRunOracleCalls
end CountingMatroid.Analysis.BoundedRunOracleCalls
namespace CountingMatroid.Analysis.ResourceBound
end CountingMatroid.Analysis.ResourceBound
set_option autoImplicit false

namespace CountingMatroid.Analysis.SuccessfulPrefixAbortBound
end CountingMatroid.Analysis.SuccessfulPrefixAbortBound
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.SuccessfulPrefixAbortBound

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.PhaseObservationExperiment

theorem CountingMatroid.Analysis.SuccessfulPrefixAbortBound.successful_prefix_has_good_cursor (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams) (j : ℕ)
    (hj : j < (CountingMatroid.Interface.Pseudocode.setup n p).L)
    (pref : List Bool) (hprefix : SuccessfulPhasePrefix n r o₁ o₂ p j pref) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let m := CountingMatroid.Model.Run.blockLength n r p
    ∃ bits : List Bool, ∃ current : AnnealingCursor n,
      bits.length = m ∧
      (∀ a < j, FirstPhaseFailure.CertifiedPhase r o₁ o₂
        (fun i => (bits[i]?).getD false) s a) ∧
      BoundedRunPhaseHistory.phaseHistory r o₁ o₂
        (fun i => (bits[i]?).getD false) s j = some current ∧
      FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂ s j current ∧
      pref = bits.take current.bitCursor ∧
      pref.length = min current.bitCursor m := by sorry
