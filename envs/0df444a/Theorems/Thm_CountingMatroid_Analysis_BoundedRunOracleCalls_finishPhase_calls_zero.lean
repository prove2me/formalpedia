-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_BoundedRunOracleCalls_finishPhase_calls_zero
-- name    : CountingMatroid.Analysis.BoundedRunOracleCalls.finishPhase_calls_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T13:10:07.0707+00:00
-- url     : https://prove2.me/theorems/53ab987d-09d7-4e3a-9575-218dfc9bb493
-- title:
--   Finishing an annealing phase makes no oracle calls
-- statement:
--   Let $n\in\mathbb N$, let $s$ be any annealing schedule, and let $j\in\mathbb N$. Let $w$ assign rational multipliers to ordered pairs of distinct ground indices, and let $a$ be any observation cursor containing a paired state, tape position, class counts, and rational numerator sum. Write $Q(A)$ for the sum of the two independence-oracle charge counters of a computation $A$. Then $$Q(\operatorname{finishPhase}(s,j,w,a))=0.$$ Forming the ratio estimate and updating multipliers therefore add no independence-oracle charge, whether the phase finishes or rejects its counts.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/BoundedRunOracleCalls.lean#L237-L270

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Dict
import Definitions.Def_CountingMatroidSupport_Computation_Heap
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Num
import Definitions.Def_CountingMatroidSupport_Computation_Queue
import Definitions.Def_CountingMatroidSupport_Computation_Rand
import Definitions.Def_CountingMatroidSupport_Computation_Roster
import Definitions.Def_CountingMatroidSupport_Computation_Slot
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroidSupport_Computation_Std
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Program
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
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF

namespace CountingMatroid.Analysis.BoundedRunOracleCalls
end CountingMatroid.Analysis.BoundedRunOracleCalls
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.ResourceBound
end CountingMatroid.Analysis.ResourceBound
set_option autoImplicit false

/-!
# Oracle charges in one capped annealing run

The bounds below sum the two supplied independence-oracle charges through
the capped loops, including abort branches.
-/

namespace CountingMatroid.Analysis.BoundedRunOracleCalls
end CountingMatroid.Analysis.BoundedRunOracleCalls
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.BoundedRunOracleCalls

open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines



open CountingMatroid.Program
open CountingMatroid.Analysis.ResourceBound

theorem CountingMatroid.Analysis.BoundedRunOracleCalls.finishPhase_calls_zero {n : ℕ} (s : AnnealingSchedule) (j : ℕ)
    (w : Multipliers n) (observed : ObservationCursor n) :
    oracleCalls (finishPhase s j w observed) = 0 := by sorry
