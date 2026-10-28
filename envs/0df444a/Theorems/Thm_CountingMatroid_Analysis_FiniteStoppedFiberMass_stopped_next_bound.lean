-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_FiniteStoppedFiberMass_stopped_next_bound
-- name    : CountingMatroid.Analysis.FiniteStoppedFiberMass.stopped_next_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:11:57.297193+00:00
-- url     : https://prove2.me/theorems/27a0a69a-fb81-4f74-b769-b34f3f42d60e
-- title:
--   A stopped next-event bound factors through its covered marginal
-- statement:
--   For a finite Boolean list $h$ and $t\in\mathbb N$, let $\omega_{h,b}$ be the infinite tape obtained by concatenating $h$ with a length-$t$ Boolean list $b$ and filling later positions with zero. For an event $E$ on tapes, write
--
--   $$\mathbb P_{h,t}(E)=2^{-t}\sum_{b\in\{0,1\}^t}\mathbf1_{E(\omega_{h,b})}.$$
--
--   This is a real-valued finite uniform average, with the prefix fixed.
--
--   Let $\alpha$ be any type and let $f$ map tapes to optional pairs $(a,b)\in\alpha\times\mathbb N$. Assume every successful return has $b\ge|h|$ and can be replayed on any tape agreeing on $[|h|,b)$. Fix $a\in\alpha$, an event $E(\omega,b)$, and $B\ge0$. For every $b$ with $|h|\le b\le|h|+t$, assume every prefix $p$ of length $b-|h|$ returning $(a,b)$ satisfies
--
--   $$\mathbb P_{h\mathbin{+\!+}p,t-(b-|h|)}\{\omega:E(\omega,b)\}\le B.$$
--
--   Then
--
--   $$\begin{aligned}
--   &\mathbb P_{h,t}\{\exists b\le|h|+t:\ f=\operatorname{some}(a,b),\ E(\omega,b)\}\\
--   &\qquad\le\mathbb P_{h,t}\{\exists b\le|h|+t:\ f=\operatorname{some}(a,b)\}\,B.
--   \end{aligned}$$
--
--   The bound applies without conditioning away failure or uncovered outcomes.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/FiniteStoppedFiberMass.lean#L189-L222

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

theorem CountingMatroid.Analysis.FiniteStoppedFiberMass.stopped_next_bound {α : Type} (head : List Bool) (t : ℕ)
    (f : (ℕ → Bool) → Option (α × ℕ))
    (hf : ChainStepIntervalReplay.SuccessReplay f Prod.snd head.length)
    (a : α) (E : (ℕ → Bool) → ℕ → Prop) (B : ℝ) (hB : 0 ≤ B)
    (hcont : ∀ stop, head.length ≤ stop → stop ≤ head.length+t →
      ∀ pref : List.Vector Bool (stop-head.length),
      f (finiteTape (head ++ pref.val)) = some (a, stop) →
      fairMass (head ++ pref.val) (t-(stop-head.length)) (fun tape => E tape stop) ≤ B) :
    fairMass head t (fun tape => ∃ stop, stop ≤ head.length + t ∧
      f tape = some (a, stop) ∧ E tape stop) ≤
    fairMass head t (fun tape => ∃ stop, stop ≤ head.length + t ∧
      f tape = some (a, stop)) * B := by sorry
