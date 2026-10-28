-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_FiniteStoppedKernelBind_stopped_kernel_bind_covered_bound
-- name    : CountingMatroid.Analysis.FiniteStoppedKernelBind.stopped_kernel_bind_covered_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:14:59.998196+00:00
-- url     : https://prove2.me/theorems/6bf3296a-0671-4823-942f-e5d34f269c93
-- title:
--   Stopped continuation bounds compose through covered finite-state marginals
-- statement:
--   For a finite Boolean list $h$ and $t\in\mathbb N$, let $\omega_{h,b}$ be the infinite tape obtained by concatenating $h$ with a length-$t$ Boolean list $b$ and filling later positions with zero. For an event $E$ on tapes, write
--
--   $$\mathbb P_{h,t}(E)=2^{-t}\sum_{b\in\{0,1\}^t}\mathbf1_{E(\omega_{h,b})}.$$
--
--   This is a real-valued finite uniform average, with the prefix fixed. Let $f$ map tapes to optional values in an arbitrary type $\alpha$, and let $c:\alpha\to\mathbb N$ be their cursor. Assume successful interval replay from $|h|$: whenever $f(\omega)=\operatorname{some}(a)$, one has $|h|\le c(a)$, and every tape agreeing with $\omega$ on $[|h|,c(a))$ returns the same $a$.
--
--   Let $\Omega$ be a finite type, let $s:\alpha\to\Omega$ extract a state from an output, let $E(\omega,a)$ be a continuation event, and let $B:\Omega\to\mathbb R$ be nonnegative. Assume every sampled full suffix on which $f$ returns $a$ and $E(\omega,a)$ holds satisfies $c(a)\le|h|+t$. For every $a$ with $|h|\le c(a)\le|h|+t$, assume every length-$(c(a)-|h|)$ prefix $p$ returning $a$ satisfies
--
--   $$\mathbb P_{h\mathbin{+\!+}p,t-(c(a)-|h|)}\{\omega:E(\omega,a)\}\le B(s(a)).$$
--
--   Then
--
--   $$\mathbb P_{h,t}\{\exists a:\ f=\operatorname{some}(a),\ E(\omega,a)\}\le\sum_{x\in\Omega}\mathbb P_{h,t}\{\exists a:\ f=\operatorname{some}(a),\ c(a)\le|h|+t,\ s(a)=x\}\,B(x).$$
--
--   This state-level form retains both abort mass and the explicit coverage restriction.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/FiniteStoppedKernelBind.lean#L94-L142

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

namespace CountingMatroid.Analysis.FiniteStoppedKernelBind
end CountingMatroid.Analysis.FiniteStoppedKernelBind
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! A finite stopped operation can be followed by a uniformly bounded fresh
continuation without conditioning away its abort mass. -/
namespace CountingMatroid.Analysis.FiniteStoppedKernelBind
end CountingMatroid.Analysis.FiniteStoppedKernelBind
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.FiniteStoppedKernelBind
open CountingMatroid.Analysis.FiniteStoppedFiberMass

theorem CountingMatroid.Analysis.FiniteStoppedKernelBind.stopped_kernel_bind_covered_bound {α Ω : Type} [Fintype Ω]
    (head : List Bool) (t : ℕ) (f : (ℕ → Bool) → Option α)
    (cursor : α → ℕ) (state : α → Ω)
    (hf : ChainStepIntervalReplay.SuccessReplay f cursor head.length)
    (E : (ℕ → Bool) → α → Prop) (B : Ω → ℝ) (hB : ∀ x, 0 ≤ B x)
    (hcovered : ∀ bits : List.Vector Bool t, ∀ a,
      f (finiteTape (head ++ bits.val)) = some a →
      E (finiteTape (head ++ bits.val)) a → cursor a ≤ head.length + t)
    (hcont : ∀ a, head.length ≤ cursor a → cursor a ≤ head.length + t →
      ∀ pref : List.Vector Bool (cursor a - head.length),
      f (finiteTape (head ++ pref.val)) = some a →
      fairMass (head ++ pref.val) (t - (cursor a - head.length))
        (fun tape => E tape a) ≤ B (state a)) :
    fairMass head t (fun tape => ∃ a, f tape = some a ∧ E tape a) ≤
      ∑ x : Ω, fairMass head t (fun tape => ∃ a, f tape = some a ∧
        cursor a ≤ head.length + t ∧ state a = x) * B x := by sorry
