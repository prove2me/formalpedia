-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_ResourceBound_median_scan_properties
-- name    : CountingMatroid.Analysis.ResourceBound.median_scan_properties
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T13:05:45.259794+00:00
-- url     : https://prove2.me/theorems/d49d0b29-413a-4fbf-befb-14b99a7e7147
-- title:
--   The median insertion scan preserves order, lengths, and rational-size bounds
-- statement:
--   Let $X,A$ be finite lists of rational numbers and $K\in\mathbb N$. Assume $A$ is nondecreasing and every entry of both lists has canonical rational encoding length at most $K$, counting sign, delimiter, and binary numerator and denominator lengths. Let $B$ be the result of inserting the entries of $X$ successively into $A$ using the program’s ordered-insertion routine. Then $$B\text{ is nondecreasing},\qquad\forall b\in B,\ \ell(b)\le K,\qquad |B|=|A|+|X|.$$ These invariants support the median routine’s correctness and work analysis.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/EstimateMedianResource.lean#L160-L192

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
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
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

theorem CountingMatroid.Analysis.ResourceBound.median_scan_properties (xs acc : List ℚ) (K : ℕ)
    (haccSort : acc.Pairwise (· ≤ ·))
    (haccSize : ∀ q ∈ acc, binaryRatLength q ≤ K)
    (hxsSize : ∀ q ∈ xs, binaryRatLength q ≤ K) :
    let out := (Arlib.Computation.Charged.foldl
      (fun acc value => CountingMatroid.Program.sortedInsert value acc)
      xs acc).val
    out.Pairwise (· ≤ ·) ∧
      (∀ q ∈ out, binaryRatLength q ≤ K) ∧
      out.length = acc.length + xs.length := by sorry
