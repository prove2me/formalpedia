-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_FiniteStoppedFiberMass_stopped_fiber_bound
-- name    : CountingMatroid.Analysis.FiniteStoppedFiberMass.stopped_fiber_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:56:59.130075+00:00
-- url     : https://prove2.me/theorems/1d53cf73-eae3-4416-b76a-d733fd282419
-- title:
--   A fixed successful stopping fiber inherits a fresh-suffix bound
-- statement:
--   For a finite Boolean list $h$ and $t\in\mathbb N$, let $\omega_{h,b}$ be the infinite tape obtained by concatenating $h$ with a length-$t$ Boolean list $b$ and filling later positions with zero. For an event $E$ on tapes, write
--
--   $$\mathbb P_{h,t}(E)=2^{-t}\sum_{b\in\{0,1\}^t}\mathbf1_{E(\omega_{h,b})}.$$
--
--   This is a real-valued finite uniform average, with the prefix fixed. Let $f$ map tapes to optional values in an arbitrary type $\alpha$, and let $c:\alpha\to\mathbb N$ be their cursor. Assume successful interval replay from $|h|$: whenever $f(\omega)=\operatorname{some}(a)$, one has $|h|\le c(a)$, and every tape agreeing with $\omega$ on $[|h|,c(a))$ returns the same $a$.
--
--   Fix $a\in\alpha$ with $|h|\le c(a)\le|h|+t$, an event $E$ on tapes, and $B\in\mathbb R$ with $B\ge0$. Put $k=c(a)-|h|$. Assume that every length-$k$ prefix $p$ satisfying $f(\omega_{h,p})=\operatorname{some}(a)$ has
--
--   $$\mathbb P_{h\mathbin{+\!+}p,t-k}(E)\le B.$$
--
--   Then
--
--   $$\mathbb P_{h,t}\{f=\operatorname{some}(a)\text{ and }E\}\le\mathbb P_{h,t}\{f=\operatorname{some}(a)\}\,B.$$
--
--   The successful fiber's mass is retained rather than divided out.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/FiniteStoppedFiberMass.lean#L74-L133

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
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformReplay
import Definitions.Def_CountingMatroid_Analysis_ChainStepIntervalReplay
import Definitions.Def_CountingMatroid_Analysis_FiniteStoppedFiberMass
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Program
import Definitions.Def_CountingMatroid_Model_Subroutines
import Lean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
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

namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! Finite uniform tape disintegration at a successful fixed endpoint cursor. -/
namespace CountingMatroid.Analysis.FiniteStoppedFiberMass
end CountingMatroid.Analysis.FiniteStoppedFiberMass
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.FiniteStoppedFiberMass

theorem CountingMatroid.Analysis.FiniteStoppedFiberMass.stopped_fiber_bound {α : Type} (head : List Bool) (t : ℕ)
    (f : (ℕ → Bool) → Option α) (cursor : α → ℕ)
    (hf : ChainStepIntervalReplay.SuccessReplay f cursor head.length)
    (a : α) (ha : head.length ≤ cursor a) (hc : cursor a ≤ head.length + t)
    (E : (ℕ → Bool) → Prop) (B : ℝ) (hB : 0 ≤ B)
    (hcont : ∀ pref : List.Vector Bool (cursor a - head.length),
      f (finiteTape (head ++ pref.val)) = some a →
      fairMass (head ++ pref.val) (t - (cursor a - head.length)) E ≤ B) :
    fairMass head t (fun tape => f tape = some a ∧ E tape) ≤
      fairMass head t (fun tape => f tape = some a) * B := by sorry
