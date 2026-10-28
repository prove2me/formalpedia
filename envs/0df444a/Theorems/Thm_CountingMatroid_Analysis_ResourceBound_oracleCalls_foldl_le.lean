-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_ResourceBound_oracleCalls_foldl_le
-- name    : CountingMatroid.Analysis.ResourceBound.oracleCalls_foldl_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T12:43:54.390888+00:00
-- url     : https://prove2.me/theorems/162a5b29-db6e-4057-b413-3c033b657580
-- title:
--   Oracle-call bound for a uniformly bounded list fold
-- statement:
--   For a charged computation $F$, let $Q(F)$ be the sum of its two original-oracle charge components, `oracleFirst` and `oracleSecond`. Let $\beta$ and $\iota$ be arbitrary state and element types. Let $f(b,a)$ be a charged state update for $b\in\beta$ and $a\in\iota$, and let $k\in\mathbb N$ satisfy $Q(f(b,a))\le k$ for every $b,a$. For any finite list $l$ of elements of $\iota$ and initial state $b$,
--   $$Q(\operatorname{foldl}(f,l,b))\le |l|k.$$
--   Here $|l|$ denotes the list length. The result bounds scans whose intermediate state evolves during computation.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/PrimitiveOracleCalls.lean#L45-L66

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
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
set_option autoImplicit false

namespace CountingMatroid.Analysis.ResourceBound
end CountingMatroid.Analysis.ResourceBound
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ResourceBound

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines
open CountingMatroid.Model.Operations

theorem CountingMatroid.Analysis.ResourceBound.oracleCalls_foldl_le {β ι : Type}
    (f : β → ι → Arlib.Computation.Charged Op Cell β) (k : ℕ)
    (h : ∀ b a, oracleCalls (f b a) ≤ k) :
    ∀ l b, oracleCalls (Arlib.Computation.Charged.foldl f l b) ≤ l.length * k := by sorry
