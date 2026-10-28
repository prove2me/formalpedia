-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_FiniteStoppedKernelBind_stopped_kernel_bind_bound
-- name    : CountingMatroid.Analysis.FiniteStoppedKernelBind.stopped_kernel_bind_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:13:39.353923+00:00
-- url     : https://prove2.me/theorems/ba28a811-23ee-4e7e-9742-c5143b2c4eb1
-- title:
--   A stopped continuation is bounded by the expected output-dependent bound
-- statement:
--   For a finite Boolean list $h$ and $t\in\mathbb N$, let $\omega_{h,b}$ be the infinite tape obtained by concatenating $h$ with a length-$t$ Boolean list $b$ and filling later positions with zero. For an event $E$ on tapes, write
--
--   $$\mathbb P_{h,t}(E)=2^{-t}\sum_{b\in\{0,1\}^t}\mathbf1_{E(\omega_{h,b})}.$$
--
--   This is a real-valued finite uniform average, with the prefix fixed. Let $f$ map tapes to optional values in an arbitrary type $\alpha$, and let $c:\alpha\to\mathbb N$ be their cursor. Assume successful interval replay from $|h|$: whenever $f(\omega)=\operatorname{some}(a)$, one has $|h|\le c(a)$, and every tape agreeing with $\omega$ on $[|h|,c(a))$ returns the same $a$.
--
--   Let $E(\omega,a)$ be a continuation event and let $B:\alpha\to\mathbb R$ be nonnegative. Assume every full sampled suffix for which both $f(\omega)=\operatorname{some}(a)$ and $E(\omega,a)$ hold satisfies $c(a)\le|h|+t$. Also assume that for every $a$ with $|h|\le c(a)\le|h|+t$, every prefix $p$ of length $c(a)-|h|$ returning $a$ satisfies
--
--   $$\mathbb P_{h\mathbin{+\!+}p,t-(c(a)-|h|)}\{\omega:E(\omega,a)\}\le B(a).$$
--
--   Define $\overline B(\operatorname{some}(a))=B(a)$ and $\overline B(\operatorname{none})=0$. Then
--
--   $$\mathbb P_{h,t}\{\exists a:\ f=\operatorname{some}(a),\ E(\omega,a)\}\le2^{-t}\sum_{b\in\{0,1\}^t}\overline B(f(\omega_{h,b})).$$
--
--   Only results participating in the continued event must be covered by the finite tape; the output type itself need not be finite.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/FiniteStoppedKernelBind.lean#L11-L92

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

theorem CountingMatroid.Analysis.FiniteStoppedKernelBind.stopped_kernel_bind_bound {α : Type} (head : List Bool) (t : ℕ)
    (f : (ℕ → Bool) → Option α) (cursor : α → ℕ)
    (hf : ChainStepIntervalReplay.SuccessReplay f cursor head.length)
    (E : (ℕ → Bool) → α → Prop) (B : α → ℝ) (hB : ∀ a, 0 ≤ B a)
    (hcovered : ∀ bits : List.Vector Bool t, ∀ a,
      f (finiteTape (head ++ bits.val)) = some a →
      E (finiteTape (head ++ bits.val)) a → cursor a ≤ head.length + t)
    (hcont : ∀ a, head.length ≤ cursor a → cursor a ≤ head.length + t →
      ∀ pref : List.Vector Bool (cursor a - head.length),
      f (finiteTape (head ++ pref.val)) = some a →
      fairMass (head ++ pref.val) (t - (cursor a - head.length))
        (fun tape => E tape a) ≤ B a) :
    fairMass head t (fun tape => ∃ a, f tape = some a ∧ E tape a) ≤
      ∑ bits : List.Vector Bool t, (1 / (2 : ℝ) ^ t) *
        ((f (finiteTape (head ++ bits.val))).map B).getD 0 := by sorry
