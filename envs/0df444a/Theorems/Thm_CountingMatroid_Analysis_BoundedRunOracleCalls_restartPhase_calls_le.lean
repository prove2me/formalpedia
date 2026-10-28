-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_BoundedRunOracleCalls_restartPhase_calls_le
-- name    : CountingMatroid.Analysis.BoundedRunOracleCalls.restartPhase_calls_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T13:04:19.857511+00:00
-- url     : https://prove2.me/theorems/fca1d4f3-7f12-426b-ac7d-4a2382f96772
-- title:
--   Restarting through $j$ kernels has a bounded oracle budget
-- statement:
--   Let $n,r\in\mathbb N$, let $o_1,o_2$ be Boolean oracles on subset indicators of an $n$-element set, and fix a tape $t:\mathbb N\to\{0,1\}$. Let $s$ be an annealing schedule, with $\tau$ trace transitions per crossed kernel and restart-attempt cap $B$. Let $U$ be any stored table assigning rational defect multipliers to each natural phase index, and let $j,c\in\mathbb N$ be the number of kernels to cross and the starting tape position. Write $Q(A)$ for the sum of the two independence-oracle charge counters of a computation $A$. Then $$Q(\operatorname{restartPhase}(r,o_1,o_2,t,s,U,j,c))\le j\tau B(4n).$$ The estimate is uniform over learned weights and covers aborted restarts.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/BoundedRunOracleCalls.lean#L171-L209

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

theorem CountingMatroid.Analysis.BoundedRunOracleCalls.restartPhase_calls_le {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (tables : LearnedWeights n)
    (j cursor : ℕ) :
    oracleCalls (restartPhase r o₁ o₂ tape s tables j cursor) ≤
      j * (s.τ * (s.restartCap * (4 * n))) := by sorry
