-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_StoppedDrawHistory_stopped_draw_history
-- name    : CountingMatroid.Analysis.StoppedDrawHistory.stopped_draw_history
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:21:05.693915+00:00
-- url     : https://prove2.me/theorems/2b8f9c35-c381-4852-a0ba-c2d294c2aae7
-- title:
--   A stable stopped draw produces a covered prefix-free history
-- statement:
--   Fix a Boolean base list $b$, a suffix length $t\in\mathbb N$, and a trial cap $T\in\mathbb N$. A stopped-draw descriptor maps a Boolean list $x$ optionally to a pair $(h,v)$, where $h$ is a consumed prefix and $v\in\mathbb N$ is the draw denominator. On every $|x|=t$ successful descriptor, assume: $h$ is a prefix of $x$; every other length-$t$ list extending $h$ gives the same pair $(h,v)$; $v>0$; and
--   $$T\bigl(\log_2(v-1)+1\bigr)\le t-|h|.$$
--   Here the logarithm is the floor natural logarithm with $\log_2 0=0$. Then there exist a finite prefix family $\mathcal H$ and a denominator assignment $d$ such that $\mathcal H$ is prefix-free, every $h\in\mathcal H$ has $|h|\le t$, $d(h)>0$, and enough suffix space for its $T$ trials. Moreover,
--   $$|x|=t\ \wedge\ \operatorname{site}(x)=(h,v)\Longrightarrow h\in\mathcal H,\quad d(h)=v,\quad h\preceq x.$$
--   The resulting history is indexed by the fixed base $b$ and supports later adaptive draw bounds.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/StoppedDrawHistory.lean#L23-L74

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
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformAbortMass
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_StoppedDrawHistory
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
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Basic
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

namespace CountingMatroid.Analysis.FiniteObservationMarkov
end CountingMatroid.Analysis.FiniteObservationMarkov
namespace CountingMatroid.Analysis.FiniteTapePrefixBound
end CountingMatroid.Analysis.FiniteTapePrefixBound
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
set_option autoImplicit false

/-!
A deterministic stopping descriptor separates operational replay from the
finite prefix-free packaging required by the adaptive draw mass bound.
-/
namespace CountingMatroid.Analysis.StoppedDrawHistory
end CountingMatroid.Analysis.StoppedDrawHistory
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.StoppedDrawHistory

theorem CountingMatroid.Analysis.StoppedDrawHistory.stopped_draw_history (base : List Bool) (t trials : ℕ)
    (draw : StoppedDraw t trials) :
    ∃ history : BoundedUniformAbortMass.DrawHistory base t trials,
      ∀ bits head v, bits.length = t → draw.site bits = some (head, v) →
        head ∈ history.prefixes ∧ history.denominator head = v ∧ head <+: bits := by sorry
