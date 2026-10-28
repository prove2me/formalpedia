-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_RestartDrawProbeScanReplay_probedBody_scan_quiet_replay
-- name    : CountingMatroid.Analysis.RestartDrawProbeScanReplay.probedBody_scan_quiet_replay
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:03:17.198719+00:00
-- url     : https://prove2.me/theorems/0464a825-77ff-4c9d-909d-4db4377d7f1b
-- title:
--   A quiet live return scan replays its entire final accumulator
-- statement:
--   Let $n,r\in\mathbb N$, let $o_1,o_2$ be Boolean query functions on subsets of $[n]$, and let $s$ be an annealing schedule. A paired state is a subset of $[n]\times\{0,1\}$; a restart cursor stores such a state, a tape position, and an attempt count. Fix a rational parameter $q$, rational defect multipliers $w(i)$ for ordered distinct empty/full pair indices $i$, a target attempt ordinal $a\in\mathbb N$, a draw index $b\in\{0,1,2\}$, and a finite list $X$ of natural numbers. Let $F_t$ denote the value of the early-stop fold of the probed return body over $X$, using Boolean tape $t:\mathbb N\to\{0,1\}$. Its accumulator consists of an optional restart cursor, a Boolean done flag, a retained attempt counter, and an optional draw descriptor $(u,D)$ recording a draw's starting tape position and range size. The probe retains its first observed descriptor. Let the initial live cursor be $v$, the initial done flag be $d$, and the retained count and lower position be $c,f\in\mathbb N$, with $f\le v.\mathrm{bitCursor}$. Start with no descriptor. Suppose the scan on $t$ finishes with no descriptor, with a live cursor $v'$, and with retained count $C\le a$. Then $$f\le v'.\mathrm{bitCursor},\qquad \bigl[t'=t\text{ on }[f,v'.\mathrm{bitCursor})\bigr]\Longrightarrow F_{t'}((v,d),c,\mathrm{none})=F_t((v,d),c,\mathrm{none}).$$ The equality includes the optional cursor, done flag, retained count, and descriptor.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/RestartDrawProbeScanReplay.lean#L423-L532

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
import Definitions.Def_CountingMatroid_Analysis_RestartDrawProbeScanReplay
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
set_option autoImplicit false

/-!
Interval replay for the concrete ordinal probe's own accumulation, confined
to one capped return scan and lifted through the transition, stage and
restart folds. A captured descriptor can only ever change at the globally
unique attempt whose running count matches the probed ordinal; before that
attempt the probe is silent, and after it the descriptor is sticky.
-/
namespace CountingMatroid.Analysis.RestartDrawProbeScanReplay
end CountingMatroid.Analysis.RestartDrawProbeScanReplay
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RestartDrawProbeScanReplay
open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.RestartDrawProbe
open CountingMatroid.Analysis.ChainStepIntervalReplay
open CountingMatroid.Analysis.ObservationRoundDrawSites
open CountingMatroid.Analysis.RestartAttemptAccounting

theorem CountingMatroid.Analysis.RestartDrawProbeScanReplay.probedBody_scan_quiet_replay {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n) (ordinal : ℕ) (draw : Fin 3) :
    ∀ (xs : List ℕ) (cur : RestartCursor n) (done : Bool) (count floor : ℕ),
      floor ≤ cur.bitCursor → ∀ (tape : ℕ → Bool) (c : RestartCursor n),
      (Arlib.Computation.Charged.foldlWhile
          (fun acc (_ : ℕ) => probedBody r o₁ o₂ tape s q w ordinal draw acc) xs
          (((some cur, done), count), none)).val.2 = none →
      (Arlib.Computation.Charged.foldlWhile
          (fun acc (_ : ℕ) => probedBody r o₁ o₂ tape s q w ordinal draw acc) xs
          (((some cur, done), count), none)).val.1.1.1 = some c →
      (Arlib.Computation.Charged.foldlWhile
          (fun acc (_ : ℕ) => probedBody r o₁ o₂ tape s q w ordinal draw acc) xs
          (((some cur, done), count), none)).val.1.2 ≤ ordinal →
      floor ≤ c.bitCursor ∧ ∀ other : ℕ → Bool,
        (∀ i, floor ≤ i → i < c.bitCursor → tape i = other i) →
        (Arlib.Computation.Charged.foldlWhile
          (fun acc (_ : ℕ) => probedBody r o₁ o₂ other s q w ordinal draw acc) xs
          (((some cur, done), count), none)).val =
        (Arlib.Computation.Charged.foldlWhile
          (fun acc (_ : ℕ) => probedBody r o₁ o₂ tape s q w ordinal draw acc) xs
          (((some cur, done), count), none)).val := by sorry
