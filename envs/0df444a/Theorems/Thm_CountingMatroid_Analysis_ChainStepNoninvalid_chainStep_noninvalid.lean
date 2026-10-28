-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_ChainStepNoninvalid_chainStep_noninvalid
-- name    : CountingMatroid.Analysis.ChainStepNoninvalid.chainStep_noninvalid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:05:54.984358+00:00
-- url     : https://prove2.me/theorems/0d771952-c32b-4411-94fa-d8196583ec53
-- title:
--   Successful chain steps preserve classifier validity
-- statement:
--   Let $n,r\in\mathbb N$, let $o_1,o_2:\{0,1\}^n\to\{0,1\}$ be fixed Boolean oracle functions, let $q\in\mathbb Q$, and let $w$ assign a rational multiplier to every ordered pair of distinct indices in $[n]=\{0,\ldots,n-1\}$. Paired states are subsets of $[n]\times\{0,1\}$. A state is classifier-valid when it is either a transversal (one element from every pair) or has exactly one empty pair and one distinct full pair, with one element from every other pair.
--
--   Fix a Boolean tape $\omega:\mathbb N\to\{0,1\}$, a rejection-trial cap $T\in\mathbb N$, a classifier-valid input state $X$, and an initial cursor $c\in\mathbb N$. For every paired state $Y$ and cursor $b\in\mathbb N$,
--
--   $$\operatorname{chainStep}(\omega,T,q,w,X,c).\mathrm{val}=\operatorname{some}(Y,b)\quad\Longrightarrow\quad \operatorname{classify}(Y)\ne\operatorname{invalid}.$$
--
--   The fixed rank parameter and oracle functions are those above. The invariant includes lazy holds and rejected proposals, and does not assume positive weights.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ChainStepNoninvalid.lean#L16-L63

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

namespace CountingMatroid.Analysis.ChainStepNoninvalid
end CountingMatroid.Analysis.ChainStepNoninvalid
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
set_option autoImplicit false

/-!
A successful operational chain attempt preserves non-invalid classification.
An invalid proposal is rejected; each other success returns either the valid
old state or the proposal whose classifier was checked. This statement does
not claim that every failure is a capped draw failure.
-/

namespace CountingMatroid.Analysis.ChainStepNoninvalid
end CountingMatroid.Analysis.ChainStepNoninvalid
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ChainStepNoninvalid

open CountingMatroid.Model CountingMatroid.Program

theorem CountingMatroid.Analysis.ChainStepNoninvalid.chainStep_noninvalid {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (trials : ℕ) (q : ℚ) (weights : Multipliers n)
    (state : PairedSet n) (cursor : ℕ) (result : PairedSet n × ℕ)
    (hvalid : (classifyState state).val ≠ .invalid)
    (h : (chainStep r o₁ o₂ tape trials q weights state cursor).val = some result) :
    (classifyState result.1).val ≠ .invalid := by sorry
