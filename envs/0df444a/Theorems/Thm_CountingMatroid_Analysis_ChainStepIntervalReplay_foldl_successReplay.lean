-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_ChainStepIntervalReplay_foldl_successReplay
-- name    : CountingMatroid.Analysis.ChainStepIntervalReplay.foldl_successReplay
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:37:09.237824+00:00
-- url     : https://prove2.me/theorems/acffdc0d-fedb-448f-b058-7a0e01499136
-- title:
--   Successful interval replay is preserved by absorbing folds
-- statement:
--   Let $\alpha,\beta$ be types and let $f$ be a tape-dependent update that takes an optional state in $\beta$ and an input in $\alpha$, returning a charged computation with an optional state. Let $c:\beta\to\mathbb N$ record the state's tape cursor. Assume that failure is absorbing, so an update of $\operatorname{none}$ always returns $\operatorname{none}$. Assume also that every update from a state $b$ has successful interval replay: if its value on tape $\omega$ is $b'$, then $c(b)\le c(b')$, and agreement of tapes on $[c(b),c(b'))$ forces the same returned value.
--
--   For any finite input list $\ell$, initial state $b$, tape $\omega$, and successful final state $d$ of the left fold $F_\ell$, one has
--
--   $$c(b)\le c(d),\qquad \omega'|_{[c(b),c(d))}=\omega|_{[c(b),c(d))}\ \Longrightarrow\ F_\ell(\omega',b)=\operatorname{some}(d).$$
--
--   The fold uses the same tape throughout. This compositional lemma transfers local tape locality to complete successful iterations.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ChainStepIntervalReplay.lean#L43-L75

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

theorem CountingMatroid.Analysis.ChainStepIntervalReplay.foldl_successReplay {α β : Type}
    (f : (ℕ → Bool) → Option β → α → Arlib.Computation.Charged Op Cell (Option β))
    (cursor : β → ℕ)
    (hnone : ∀ tape a, (f tape none a).val = none)
    (hstep : ∀ b a, SuccessReplay (fun tape => (f tape (some b) a).val)
      cursor (cursor b)) (xs : List α) (b : β) :
    SuccessReplay (fun tape =>
      (Arlib.Computation.Charged.foldl (f tape) xs (some b)).val) cursor (cursor b) := by sorry
