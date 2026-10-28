-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_BoundedRunOracleCalls_oracleCalls_foldlWhile_bound
-- name    : CountingMatroid.Analysis.BoundedRunOracleCalls.oracleCalls_foldlWhile_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T12:53:02.504994+00:00
-- url     : https://prove2.me/theorems/1d07e245-c412-4c9d-9f4d-67c248ac747c
-- title:
--   Uniform oracle-charge bound for an early-stopping fold
-- statement:
--   Let $\alpha$ be an input type and $\beta$ an accumulator type. Let $f$ assign to each $b\in\beta$ and $a\in\alpha$ a charged computation returning either a new accumulator or a stop signal. For a finite list $l$ of inputs, $\operatorname{foldWhile}(f,l,b)$ applies these computations from left to right, continuing with the returned accumulator and stopping when a step signals stop. The stopping step's charges are retained. Write $\operatorname{oc}(P)$ for the sum of the first- and second-oracle counters of a charged computation $P$. Let $K\in\mathbb N$ and assume $$\operatorname{oc}(f(b,a))\le K\qquad(b\in\beta,\ a\in\alpha).$$ For every finite list $l$ and every initial accumulator $b\in\beta$, $$\operatorname{oc}(\operatorname{foldWhile}(f,l,b))\le |l|K.$$
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/BoundedRunOracleCalls.lean#L75-L94

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

theorem CountingMatroid.Analysis.BoundedRunOracleCalls.oracleCalls_foldlWhile_bound {α β : Type}
    (f : β → α → Arlib.Computation.Charged Op Cell (Option β)) (k : ℕ)
    (hf : ∀ b a, oracleCalls (f b a) ≤ k) (l : List α) (b : β) :
    oracleCalls (Arlib.Computation.Charged.foldlWhile f l b) ≤ l.length * k := by sorry
