-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_ReturnAttemptTail_attempt_scan_tail
-- name    : CountingMatroid.Analysis.ReturnAttemptTail.attempt_scan_tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:31:39.902888+00:00
-- url     : https://prove2.me/theorems/fa8cb00c-9e4e-4e5f-a65d-af1dc034cb27
-- title:
--   Finite-tape return attempts are bounded by the ideal survival tail
-- statement:
--   Let $n,r\in\mathbb N$, let $o_1,o_2$ be Boolean query functions on subsets of $[n]$, and let $s$ be an annealing schedule. A paired state is a subset of $[n]\times\{0,1\}$; a restart cursor stores such a state, a tape position, and an attempt count. Fix rational $q$, rational defect multipliers $w$, and a finite Markov transition matrix $P$ on the paired-state space $\Omega$. For a finite Boolean prefix $h$ and $t\in\mathbb N$, let $\mu_{h,t}(E)$ be the probability of $E$ when $t$ independent fair bits are appended to $h$ and the tape is padded by zeros thereafter. Write $\operatorname{Step}_\omega(x,c)$ for the optional state-position result of the chain step on tape $\omega$, using $s.\mathrm{drawTrials},q,w$.
--
--   Assume that for every $h,t,x,y$, whenever $x$ is valid (classification not invalid), $$\mu_{h,t}\{\omega:\exists u\le |h|+t,\ \operatorname{Step}_\omega(x,|h|)=\operatorname{some}(y,u)\}\le P(x,y).$$ Let $\mathcal I$ be any predicate on restart cursors, and $\lambda\in\mathbb N$. Assume for every tape $\omega$, cursor $v$, state $y$, and position $u$ that $$\mathcal I(v),\ v.\mathrm{attempts}<s.\mathrm{restartCap},\ \operatorname{Step}_\omega(v.\mathrm{state},v.\mathrm{bitCursor})=\operatorname{some}(y,u)$$ imply $u\le\lambda$ and $\mathcal I(y,u,v.\mathrm{attempts}+1)$.
--
--   Let $k,m,t\in\mathbb N$, let $h$ be a finite Boolean prefix, and let $v$ be a valid cursor satisfying $\mathcal I(v)$, $v.\mathrm{bitCursor}=|h|$, and $|h|+t=\lambda$. Let $N_k(v,\omega)$ count permitted chain-step attempts in a scan of horizon $k$, including the attempt that fails, stopping on failure, a transversal return, or cap refusal. Let $A\subseteq\Omega$ be the transversal states. Define $$S_0(x)=\mathbf1_{x\notin A},\quad S_{a+1}(x)=\mathbf1_{x\notin A}\sum_yP(x,y)S_a(y),$$ and $$H_0(x)=1,\qquad H_{a+1}(x)=\sum_yP(x,y)S_a(y).$$ Then $$\mu_{h,t}\{\omega:m+1\le N_k(v,\omega)\}\le H_m(v.\mathrm{state}).$$
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ReturnAttemptTail.lean#L202-L322

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
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_Dirichlet
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_HittingTime
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_PotentialDecay
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_SpectralGap
import Definitions.Def_CountingMatroidSupport_Probability_Bilinear
import Definitions.Def_CountingMatroidSupport_Probability_FinDist
import Definitions.Def_CountingMatroidSupport_Probability_FinDistFunctional
import Definitions.Def_CountingMatroid_Analysis_AnnealingPartitionDrift
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhase
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseHistory
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseWork
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformAbortMass
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformReplay
import Definitions.Def_CountingMatroid_Analysis_CappedTraceReturnSubkernel
import Definitions.Def_CountingMatroid_Analysis_ChainStepIntervalReplay
import Definitions.Def_CountingMatroid_Analysis_DefectPartitionPositive
import Definitions.Def_CountingMatroid_Analysis_EmpiricalPhaseCertificate
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseEmpiricalUpdate
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseWork
import Definitions.Def_CountingMatroid_Analysis_FiniteStoppedFiberMass
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_InitialMultipliersGood
import Definitions.Def_CountingMatroid_Analysis_ObservePhaseWork
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseMeanCertificate
import Definitions.Def_CountingMatroid_Analysis_PhaseObservationExperiment
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_PositiveTimeTraceKernel
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Definitions.Def_CountingMatroid_Analysis_RestartAttemptAccounting
import Definitions.Def_CountingMatroid_Analysis_ReturnAttemptTail
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
import Definitions.Def_CountingMatroid_Analysis_StationaryMeanIdentities
import Definitions.Def_CountingMatroid_Analysis_StationaryReturnOccupation
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
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Vector
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
import Mathlib.Topology.Order.MonotoneConvergence

namespace Arlib.MarkovChains
end Arlib.MarkovChains
namespace Arlib.MarkovChains.FinChain
end Arlib.MarkovChains.FinChain
namespace Arlib.MarkovChains.FinKernel
end Arlib.MarkovChains.FinKernel
namespace Arlib
end Arlib
namespace Arlib.Probability
end Arlib.Probability
namespace Arlib.Probability.FinDist
end Arlib.Probability.FinDist
namespace Arlib.Probability.FinKernel
end Arlib.Probability.FinKernel
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace CountingMatroid.Analysis.ChainStepNoninvalid
end CountingMatroid.Analysis.ChainStepNoninvalid
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
set_option backward.isDefEq.respectTransparency false

/-!
The number of `chainStep` attempts made by one actual positive-time return,
as a value recursion. The instrumented return adds exactly this number to its
retained counter, including the attempt that ends in a draw abort. On a fresh
finite suffix whose every attempted step stays inside the block, the chance of
making more than m attempts is at most the ideal positive-time survival tail.
-/
namespace CountingMatroid.Analysis.ReturnAttemptTail
end CountingMatroid.Analysis.ReturnAttemptTail
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ReturnAttemptTail

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.FiniteStoppedFiberMass
open CountingMatroid.Analysis.PositiveTimeTraceKernel
open CountingMatroid.Analysis.RestartAttemptAccounting
open Arlib.Probability Arlib.MarkovChains

theorem CountingMatroid.Analysis.ReturnAttemptTail.attempt_scan_tail {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (P : FinChain (PairedSet n))
    (hstep : ∀ (head : List Bool) (t : ℕ) (x y : PairedSet n),
      (classifyState x).val ≠ .invalid →
      fairMass head t (fun tape => ∃ stop, stop ≤ head.length + t ∧
        (chainStep r o₁ o₂ tape s.drawTrials q w x head.length).val = some (y, stop)) ≤ P x y)
    (Inv : RestartCursor n → Prop) (lim : ℕ)
    (hinv : ∀ (tape : ℕ → Bool) (current : RestartCursor n) (y : PairedSet n) (stop : ℕ),
      Inv current → current.attempts < s.restartCap →
      (chainStep r o₁ o₂ tape s.drawTrials q w current.state current.bitCursor).val =
        some (y, stop) →
      stop ≤ lim ∧ Inv ⟨y, stop, current.attempts + 1⟩)
    (k m : ℕ) (head : List Bool) (t : ℕ) (current : RestartCursor n)
    (hcursor : current.bitCursor = head.length) (hlim : head.length + t = lim)
    (hvalid : (classifyState current.state).val ≠ .invalid) (hcur : Inv current) :
    fairMass head t (fun tape => m + 1 ≤ attemptScan r o₁ o₂ tape s q w k current) ≤
      tailWeight P (Finset.univ.filter
        (fun x => (classifyState x).val = .transversal)) m current.state := by sorry
