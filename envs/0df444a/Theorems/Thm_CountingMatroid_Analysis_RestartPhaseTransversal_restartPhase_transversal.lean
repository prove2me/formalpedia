-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_RestartPhaseTransversal_restartPhase_transversal
-- name    : CountingMatroid.Analysis.RestartPhaseTransversal.restartPhase_transversal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:39:26.885879+00:00
-- url     : https://prove2.me/theorems/e6348a81-5097-4bce-baad-5222d636adf6
-- title:
--   Every successful restart phase returns a transversal
-- statement:
--   Let $n,r\in\mathbb N$, let $o_1,o_2$ be Boolean query functions on subsets of $[n]$, and let $s$ be an annealing schedule. A paired state is a subset of $[n]\times\{0,1\}$; a restart cursor stores such a state, a tape position, and an attempt count. Fix any Boolean tape $t$, stored rational multiplier tables $W$ indexed by phase, stage count $j\in\mathbb N$, and starting tape position $c\in\mathbb N$. If the restart succeeds with paired state $x$ and final position $u$, then $$\operatorname{classify}(x)=\mathrm{transversal}.$$ A transversal contains exactly one label from each of the $n$ pairs.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/RestartPhaseTransversal.lean#L168-L237

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
import Definitions.Def_CountingMatroid_Analysis_ChainStepIntervalReplay
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
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

namespace CountingMatroid.Analysis.RestartPhaseTransversal
end CountingMatroid.Analysis.RestartPhaseTransversal
namespace CountingMatroid.Analysis.RestartPhaseIntervalReplay
end CountingMatroid.Analysis.RestartPhaseIntervalReplay
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
namespace CountingMatroid.Analysis.TraceReturnIntervalReplay
end CountingMatroid.Analysis.TraceReturnIntervalReplay
set_option autoImplicit false

/-!
Every successful capped return ends in the transversal class. Consequently
successful restarts return a transversal, including phases with no crossed
levels or no trace transitions. These are deterministic operational facts;
they make no probability or finite-tape coverage claim.
-/

namespace CountingMatroid.Analysis.RestartPhaseTransversal
end CountingMatroid.Analysis.RestartPhaseTransversal
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RestartPhaseTransversal

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program

theorem CountingMatroid.Analysis.RestartPhaseTransversal.restartPhase_transversal {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (tables : LearnedWeights n) (j cursor : ℕ)
    (result : PairedSet n × ℕ)
    (h : (restartPhase r o₁ o₂ tape s tables j cursor).val = some result) :
    (classifyState result.1).val = .transversal := by sorry
