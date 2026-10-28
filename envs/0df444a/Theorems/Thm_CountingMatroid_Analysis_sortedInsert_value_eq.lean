-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_sortedInsert_value_eq
-- name    : CountingMatroid.Analysis.sortedInsert_value_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T11:59:54.273235+00:00
-- url     : https://prove2.me/theorems/314a3f09-313c-4ca4-b41f-3de4a57dbf59
-- title:
--   The charged insertion scan agrees with ordered insertion on sorted lists
-- statement:
--   Let $v\in\mathbb Q$, and let $l=(x_1,\ldots,x_m)$ be a finite rational list satisfying $x_i\le x_j$ whenever $i<j$. Let $\operatorname{sortedInsert}(v,l)$ be the charged scan that inserts $v$ before the first strictly larger entry, appending it if no such entry is found. Let $\operatorname{insert}_{\le}(v,l)$ insert $v$ before the first entry at least $v$, likewise appending if there is none. The returned lists agree exactly: $$\operatorname{value}(\operatorname{sortedInsert}(v,l))=\operatorname{insert}_{\le}(v,l).$$
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/SortedInsertValue.lean#L16-L126

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
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

/-!
# Value of the charged rational insertion scan

On a sorted list, the charged scan inserts a rational at the same position as
`List.orderedInsert`. The proof first identifies the scan with strict insertion,
then uses sortedness to handle repeated values.
-/

set_option autoImplicit false

namespace CountingMatroid.Analysis
end CountingMatroid.Analysis
open CountingMatroid CountingMatroid.Analysis

theorem CountingMatroid.Analysis.sortedInsert_value_eq (value : ℚ) (sorted : List ℚ)
    (hsorted : sorted.Pairwise (· ≤ ·)) :
    (CountingMatroid.Program.sortedInsert value sorted).val =
      sorted.orderedInsert (· ≤ ·) value := by sorry
