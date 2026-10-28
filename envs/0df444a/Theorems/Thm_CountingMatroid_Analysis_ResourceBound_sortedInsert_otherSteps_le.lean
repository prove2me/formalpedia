-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_ResourceBound_sortedInsert_otherSteps_le
-- name    : CountingMatroid.Analysis.ResourceBound.sortedInsert_otherSteps_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T12:43:53.982972+00:00
-- url     : https://prove2.me/theorems/275b9162-c7e1-485e-81d4-747bf8569ed1
-- title:
--   Inserting one bounded-length rational has linear charged work
-- statement:
--   Write $W(A)$ for a computation’s charged nonoracle operations, consisting of fair-bit reads and named word-operation charges. For a reduced rational $a/b$ with $b>0$, let $\ell(a/b)$ be two plus the binary lengths of $|a|$ and $b$, assigning one digit to zero. Let $v\in\mathbb Q$, let $A$ be any finite rational list, and let $K\in\mathbb N$. Assume $\ell(v)\le K$ and $\ell(a)\le K$ for every entry $a$ of $A$. Then $$W(\operatorname{sortedInsert}(v,A))\le(|A|+1)(2K+6).$$ The routine scans the list, inserts before the first larger entry, or appends if necessary. This cost bound does not require $A$ to be sorted.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/EstimateMedianResource.lean#L72-L158

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

namespace CountingMatroid.Analysis.ResourceBound
end CountingMatroid.Analysis.ResourceBound
namespace CountingMatroid.Analysis
end CountingMatroid.Analysis
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
/-!
# Resource bounds for the charged rational median

The insertion scan preserves sorted values and has polynomial charged cost
when its input rational encodings have a common bound.
-/

set_option autoImplicit false

namespace CountingMatroid.Analysis.ResourceBound
end CountingMatroid.Analysis.ResourceBound
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ResourceBound

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines
open CountingMatroid.Model.Operations

theorem CountingMatroid.Analysis.ResourceBound.sortedInsert_otherSteps_le (value : ℚ) (sorted : List ℚ) (K : ℕ)
    (hv : binaryRatLength value ≤ K)
    (hs : ∀ q ∈ sorted, binaryRatLength q ≤ K) :
    otherSteps (CountingMatroid.Program.sortedInsert value sorted) ≤
      (sorted.length + 1) * (2 * K + 6) := by sorry
