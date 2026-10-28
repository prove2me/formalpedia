-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_RestartReturnAbortAttribution_return_attribution
-- name    : CountingMatroid.Analysis.RestartReturnAbortAttribution.return_attribution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:34:13.013582+00:00
-- url     : https://prove2.me/theorems/73ca07ab-bbf2-44e5-a299-f5e1d9674b9c
-- title:
--   Every capped return abort is attributed to its cap or a captured failed draw
-- statement:
--   Let $n,r\in\mathbb N$, let $o_1,o_2$ be Boolean query functions on subsets of $[n]$, and let $s$ be an annealing schedule. A paired state is a subset of $[n]\times\{0,1\}$; a restart cursor stores such a state, a tape position, and an attempt count. Fix a Boolean tape $t$, rational parameter $q$, and rational defect multipliers $w$. Write $A=s.\mathrm{restartCap}$ and $T=s.\mathrm{drawTrials}$. A state is valid if classification is not invalid: it is either a transversal or has exactly one empty pair and one full pair, all other pairs being singletons. Let $v$ be an initial valid restart cursor and $c\in\mathbb N$ with $v.\mathrm{attempts}=c$. A probe at ordinal $a$ and draw index $b\in\{0,1,2\}$ records a descriptor $(u,D)$ for that draw's starting tape position and range size. Let the complete counted return from $v$ with retained count $c$ have value $(z,C)$. Then $$c\le C,$$ and at least one of the following holds.
--
--   1. $z=\operatorname{some}v'$ for a valid cursor $v'$ satisfying $v'.\mathrm{attempts}=C$. Every probe with $a\ge C$ and $b\in\{0,1,2\}$, initially unobserved, returns exactly $((z,C),\mathrm{none})$.
--   2. $z=\mathrm{none}$ and $A\le C$.
--   3. $z=\mathrm{none}$ and there exist $a,b,u,D$ with $c\le a<A$ such that the $T$-trial bounded uniform draw of range $D$ at position $u$ fails, and the corresponding return probe records $(u,D)$.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/RestartReturnAbortAttribution.lean#L377-L421

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
import Definitions.Def_CountingMatroid_Analysis_RestartReturnAbortAttribution
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

namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
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
namespace CountingMatroid.Analysis.ChainStepNoninvalid
end CountingMatroid.Analysis.ChainStepNoninvalid
namespace CountingMatroid.Analysis.ObservationRoundDrawSites
end CountingMatroid.Analysis.ObservationRoundDrawSites
namespace CountingMatroid.Analysis.ClassifiedStateSelection
end CountingMatroid.Analysis.ClassifiedStateSelection
set_option autoImplicit false

/-!
Return-level abort attribution for one capped return scan. A return either
reaches a non-invalid continuing state, exhausts the shared attempt cap, or
aborts at a draw whose descriptor is captured by a concrete sticky probe
with the right ordinal. A probe whose ordinal is at least the return's final
count cannot be disturbed by this return's own processing.
-/
namespace CountingMatroid.Analysis.RestartReturnAbortAttribution
end CountingMatroid.Analysis.RestartReturnAbortAttribution
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RestartReturnAbortAttribution

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.RestartAttemptAccounting
open CountingMatroid.Analysis.RestartDrawProbe
open CountingMatroid.Analysis.ObservationRoundDrawSites



variable {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
  (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)

theorem CountingMatroid.Analysis.RestartReturnAbortAttribution.return_attribution (start : RestartCursor n) (count : ℕ)
    (hvalid : (classifyState start.state).val ≠ .invalid) (hinv : start.attempts = count) :
    count ≤ (countedReturn r o₁ o₂ tape s q w start count).val.2 ∧
    ((∃ final : RestartCursor n,
        (countedReturn r o₁ o₂ tape s q w start count).val.1 = some final ∧
        (classifyState final.state).val ≠ .invalid ∧
        final.attempts = (countedReturn r o₁ o₂ tape s q w start count).val.2 ∧
        ∀ ordinal (draw : Fin 3),
          (countedReturn r o₁ o₂ tape s q w start count).val.2 ≤ ordinal →
          (probedReturn r o₁ o₂ tape s q w ordinal draw start count none).val =
            ((countedReturn r o₁ o₂ tape s q w start count).val, none))
      ∨ (s.restartCap ≤ (countedReturn r o₁ o₂ tape s q w start count).val.2 ∧
          (countedReturn r o₁ o₂ tape s q w start count).val.1 = none)
      ∨ (∃ (ordinal : ℕ) (draw : Fin 3) (d : ℕ × ℕ), count ≤ ordinal ∧ ordinal < s.restartCap ∧
          (countedReturn r o₁ o₂ tape s q w start count).val.1 = none ∧
          (boundedUniform tape s.drawTrials d.2 d.1).val.1 = none ∧
          (probedReturn r o₁ o₂ tape s q w ordinal draw start count none).val.2 = some d)) := by sorry
