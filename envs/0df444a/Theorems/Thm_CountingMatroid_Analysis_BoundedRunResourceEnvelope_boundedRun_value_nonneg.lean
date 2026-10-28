-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_BoundedRunResourceEnvelope_boundedRun_value_nonneg
-- name    : CountingMatroid.Analysis.BoundedRunResourceEnvelope.boundedRun_value_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:37:49.360879+00:00
-- url     : https://prove2.me/theorems/bf331d38-b933-4612-aecd-4f77c5b05e6b
-- title:
--   Nonnegativity of the bounded annealing estimate
-- statement:
--   Let $n,r\in\mathbb N$, let $o_1,o_2$ be arbitrary Boolean subset-oracle functions on an $n$-element ground set, let $\omega$ be any Boolean tape, and let $s$ be an annealing schedule with $\rho\ge0$. Let $Z$ be the rational output of the bounded annealing run started at tape cursor zero. Then
--
--   $$Z\ge0.$$
--
--   This includes executions that abort, for which the program returns zero. It provides a deterministic output invariant without assuming that the supplied oracles describe matroids.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/BoundedRunResourceEnvelope.lean#L141-L232

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
namespace CountingMatroid.Analysis.BoundedRunOracleCalls
end CountingMatroid.Analysis.BoundedRunOracleCalls
namespace CountingMatroid.Analysis.ResourceBound
end CountingMatroid.Analysis.ResourceBound
/-!
Polynomial output encoding length is proved for every schedule and execution,
using additive observation heights and a phase-product invariant. Nonnegativity
and the zero-phase costs are also proved here. The complete resource envelope
uses separate oracle-call and nonoracle-work obligations; those dependencies
must be closed before the envelope has a complete proof.
-/

set_option autoImplicit false

namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope
end CountingMatroid.Analysis.BoundedRunResourceEnvelope
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.BoundedRunResourceEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines

theorem CountingMatroid.Analysis.BoundedRunResourceEnvelope.boundedRun_value_nonneg (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (hρ : 0 ≤ s.ρ) :
    0 ≤ (CountingMatroid.Program.boundedRun r o₁ o₂ tape s 0).val.1 := by sorry
