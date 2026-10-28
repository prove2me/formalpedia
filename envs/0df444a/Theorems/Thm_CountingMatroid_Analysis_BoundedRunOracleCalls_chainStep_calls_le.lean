-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_BoundedRunOracleCalls_chainStep_calls_le
-- name    : CountingMatroid.Analysis.BoundedRunOracleCalls.chainStep_calls_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T12:56:14.692284+00:00
-- url     : https://prove2.me/theorems/56071ec9-0715-40d2-9928-d4560dfcf60e
-- title:
--   One exchange step uses at most $4n$ oracle charges
-- statement:
--   Let $n,r\in\mathbb N$, let $o_1,o_2$ be Boolean oracles on subset indicators of an $n$-element set, and fix a tape $t:\mathbb N\to\{0,1\}$. Fix a natural draw-trial cap $T$, a rational weight parameter $q$, a rational multiplier $w_{ef}$ for every ordered pair $e\ne f$, a paired subset $X\subseteq[n]\times\{0,1\}$, and a natural tape position $c$. Write $Q(A)$ for the sum of the two independence-oracle charge counters of a computation $A$. The capped exchange step satisfies $$Q(\operatorname{chainStep}(r,o_1,o_2,t,T,q,w,X,c))\le4n.$$ The bound includes holds, rejected proposals, and aborted draws; no matroid-correctness or state-validity promise is required. It supplies a uniform budget for the bounded trajectory loops.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/BoundedRunOracleCalls.lean#L96-L130

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

theorem CountingMatroid.Analysis.BoundedRunOracleCalls.chainStep_calls_le {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (trials : ℕ) (q : ℚ) (w : Multipliers n)
    (state : PairedSet n) (cursor : ℕ) :
    oracleCalls (chainStep r o₁ o₂ tape trials q w state cursor) ≤ 4 * n := by sorry
