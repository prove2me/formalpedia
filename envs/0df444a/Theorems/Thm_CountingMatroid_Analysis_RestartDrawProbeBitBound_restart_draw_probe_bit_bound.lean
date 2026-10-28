-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_RestartDrawProbeBitBound_restart_draw_probe_bit_bound
-- name    : CountingMatroid.Analysis.RestartDrawProbeBitBound.restart_draw_probe_bit_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:02:34.577547+00:00
-- url     : https://prove2.me/theorems/7024b5b8-007a-4b42-8799-a5ceaa44f6ad
-- title:
--   A captured restart draw fits the shared bit budget
-- statement:
--   Let $n,r\in\mathbb N$ and let $o_1,o_2$ be arbitrary Boolean functions on subset queries of $E_n=\{0,\ldots,n-1\}$. A paired state is a subset of $E_n\times\{0,1\}$, and a restart record consists of such a state, a natural bit cursor, and a natural attempt count. Let $s$ be an arbitrary annealing schedule, with cooling parameter $\rho\in\mathbb Q$, phase count $L$, transitions per stage $\tau$, shared restart-attempt cap $R$, and rejection-trial cap $T$. Let $W_a(i,k)\in\mathbb Q$ be arbitrary stored weights, indexed by $a\in\mathbb N$ and distinct $i,k\in E_n$. Fix a tape and $j,c_0,K\in\mathbb N$ with $j\le L$. For $m\in\mathbb N$, define $\lambda(m)=\lfloor\log_2m\rfloor+1$ when $m>0$ and $\lambda(0)=1$. For reduced $a/b\in\mathbb Q$ with $b>0$, put $\ell(a/b)=2+\lambda(|a|)+\lambda(b)$. Suppose $$\ell(1)+n\bigl(\ell(1)+L\ell(\rho)\bigr)\le K,\qquad\ell(W_a(i,k))\le K$$ for every natural level $a$ and distinct pair $i,k$. A restart from cursor $c_0$ first draws a transversal using $n$ tape bits, then processes stages $a=1,\ldots,j$ at parameter $\rho^a$ and weights $W_a$, making $\tau$ trace-return transitions per stage under the shared attempt cap. The counted version retains an auxiliary number of actual chain-step calls even if the public result aborts. Write $w(v)=\log_2(v-1)+1$, using truncated natural subtraction and the natural logarithm convention $\log_2 0=0$. This is the trial-width bound for denominator $v$. For any ordinal $a\in\mathbb N$ and draw label $b\in\{0,1,2\}$, if the observed restart captures descriptor $(c,v)$, then $$c+Tw(v)\le c_0+n+R\bigl(1+3T(4K+n+1)\bigr).$$
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/RestartDrawProbeBitBound.lean#L252-L305

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
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformAbortMass
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformReplay
import Definitions.Def_CountingMatroid_Analysis_ChainDrawSiteReplay
import Definitions.Def_CountingMatroid_Analysis_ChainStepIntervalReplay
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
import Definitions.Def_CountingMatroid_Analysis_RestartAttemptAccounting
import Definitions.Def_CountingMatroid_Analysis_RestartDrawProbe
import Definitions.Def_CountingMatroid_Analysis_RestartDrawProbeBitBound
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
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Infix
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
namespace CountingMatroid.Analysis.ChainStepBitBound
end CountingMatroid.Analysis.ChainStepBitBound
namespace CountingMatroid.Analysis.FiniteObservationMarkov
end CountingMatroid.Analysis.FiniteObservationMarkov
namespace CountingMatroid.Analysis.FiniteTapePrefixBound
end CountingMatroid.Analysis.FiniteTapePrefixBound
namespace CountingMatroid.Analysis.InitialRestartLaw
end CountingMatroid.Analysis.InitialRestartLaw
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
namespace CountingMatroid.Analysis.SuccessfulPrefixAbortBound
end CountingMatroid.Analysis.SuccessfulPrefixAbortBound
namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope
end CountingMatroid.Analysis.BoundedRunResourceEnvelope
namespace CountingMatroid.Analysis.BoundedRunOtherSteps
end CountingMatroid.Analysis.BoundedRunOtherSteps
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
set_option backward.isDefEq.respectTransparency false

/-!
Quantitative bit-cursor coverage for a single probed restart ordinal,
retained even when the probed attempt later aborts. The argument mirrors
the chain/restart bit-budget invariant used for a completed restart, but
tracks the first captured draw descriptor instead of the loop's final
output.
-/
namespace CountingMatroid.Analysis.RestartDrawProbeBitBound
end CountingMatroid.Analysis.RestartDrawProbeBitBound
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RestartDrawProbeBitBound

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.RestartAttemptAccounting
open CountingMatroid.Analysis.RestartDrawProbe
open CountingMatroid.Analysis.ObservationRoundDrawSites
open CountingMatroid.Analysis.ChainStepBitBound
open CountingMatroid.Analysis.BoundedRunResourceEnvelope

theorem CountingMatroid.Analysis.RestartDrawProbeBitBound.restart_draw_probe_bit_bound {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (tables : LearnedWeights n)
    (j cursor K : ℕ) (hj : j ≤ s.L)
    (hq : binaryRatLength 1 + n * (binaryRatLength 1 + s.L * binaryRatLength s.ρ) ≤ K)
    (hw : ∀ phase i, binaryRatLength (tables phase i) ≤ K)
    (ordinal : ℕ) (draw : Fin 3) (d : ℕ × ℕ)
    (h : (probedRestart r o₁ o₂ tape s tables j cursor ordinal draw).val.2 = some d) :
    d.1 + s.drawTrials * ((d.2 - 1).log2 + 1) ≤
      cursor + n + s.restartCap * (1 + 3 * s.drawTrials * (4 * K + n + 1)) := by sorry
