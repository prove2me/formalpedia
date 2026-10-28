-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_FiniteStoppedFiberMass_fairMass_stop_sum
-- name    : CountingMatroid.Analysis.FiniteStoppedFiberMass.fairMass_stop_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:06:07.685718+00:00
-- url     : https://prove2.me/theorems/c5c26068-7616-44d4-a2cc-f6cf622e7b67
-- title:
--   Covered stopping-cursor events are disjoint sums of cursor fibers
-- statement:
--   For a finite Boolean list $h$ and $t\in\mathbb N$, let $\omega_{h,b}$ be the infinite tape obtained by concatenating $h$ with a length-$t$ Boolean list $b$ and filling later positions with zero. For an event $E$ on tapes, write
--
--   $$\mathbb P_{h,t}(E)=2^{-t}\sum_{b\in\{0,1\}^t}\mathbf1_{E(\omega_{h,b})}.$$
--
--   This is a real-valued finite uniform average, with the prefix fixed.
--
--   Let $\alpha$ be any type, let $f$ map tapes to optional pairs in $\alpha\times\mathbb N$, fix $a\in\alpha$, and let $E(\omega,b)$ be an event depending on a tape and a proposed stopping cursor. Then
--
--   $$\begin{aligned}
--   &\mathbb P_{h,t}\{\exists b\le|h|+t:\ f(\omega)=\operatorname{some}(a,b),\ E(\omega,b)\}\\
--   &\qquad=\sum_{b=0}^{|h|+t}\mathbb P_{h,t}\{f(\omega)=\operatorname{some}(a,b),\ E(\omega,b)\}.
--   \end{aligned}$$
--
--   No replay or cursor-monotonicity assumption is required for this disjointness identity.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/FiniteStoppedFiberMass.lean#L154-L187

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

theorem CountingMatroid.Analysis.FiniteStoppedFiberMass.fairMass_stop_sum {α : Type} (head : List Bool) (t : ℕ)
    (f : (ℕ → Bool) → Option (α × ℕ)) (a : α) (E : (ℕ → Bool) → ℕ → Prop) :
    fairMass head t (fun tape => ∃ stop, stop ≤ head.length + t ∧
      f tape = some (a, stop) ∧ E tape stop) =
    ∑ stop : Fin (head.length + t + 1),
      fairMass head t (fun tape => f tape = some (a, stop.val) ∧ E tape stop.val) := by sorry
