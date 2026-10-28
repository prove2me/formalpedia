-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_ChainStepIntervalReplay_successReplay_bind
-- name    : CountingMatroid.Analysis.ChainStepIntervalReplay.successReplay_bind
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:06:29.988473+00:00
-- url     : https://prove2.me/theorems/c901d423-4388-4e4a-ae2b-83d79db43bab
-- title:
--   Successful interval replay is preserved by sequential composition
-- statement:
--   Let $\mathcal T=\mathbb N\to\{0,1\}$, let $f:\mathcal T\to\operatorname{Option}(A)$ and $g:\mathcal T\times A\to\operatorname{Option}(B)$, and let $c_A:A\to\mathbb N$, $c_B:B\to\mathbb N$ be cursor maps. Fix $s\in\mathbb N$. Assume a successful result $f(\tau)=a$ has $s\le c_A(a)$ and is reproduced by every tape agreeing with $\tau$ on $[s,c_A(a))$. For every $a$, assume a successful $g(\tau,a)=b$ has $c_A(a)\le c_B(b)$ and is reproduced under agreement on $[c_A(a),c_B(b))$. Let $F$ first run $f$ and, on success, run $g$ with that result, propagating failure. Then $$F(\tau)=b\Longrightarrow s\le c_B(b)\ \text{and}\ \bigl(\tau'|_{[s,c_B(b))}=\tau|_{[s,c_B(b))}\Longrightarrow F(\tau')=b\bigr).$$
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ChainStepIntervalReplay.lean#L23-L41

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

namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
set_option autoImplicit false

/-!
Success-path replay for the charged chain step. A successful transition has
a monotone cursor and depends only on its consumed bit interval. The generic
option-fold lemma also retains the program's absorbing abort state.
-/

namespace CountingMatroid.Analysis.ChainStepIntervalReplay
end CountingMatroid.Analysis.ChainStepIntervalReplay
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ChainStepIntervalReplay
open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.BoundedUniformReplay

theorem CountingMatroid.Analysis.ChainStepIntervalReplay.successReplay_bind {α β : Type} (f : (ℕ → Bool) → Option α)
    (g : (ℕ → Bool) → α → Option β) (ca : α → ℕ) (cb : β → ℕ) (start : ℕ)
    (hf : SuccessReplay f ca start)
    (hg : ∀ a, SuccessReplay (fun tape => g tape a) cb (ca a)) :
    SuccessReplay (fun tape => (f tape).bind (g tape)) cb start := by sorry
