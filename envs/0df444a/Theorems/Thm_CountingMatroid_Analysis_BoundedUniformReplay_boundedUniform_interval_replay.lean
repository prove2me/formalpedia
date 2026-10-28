-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_BoundedUniformReplay_boundedUniform_interval_replay
-- name    : CountingMatroid.Analysis.BoundedUniformReplay.boundedUniform_interval_replay
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:06:04.068666+00:00
-- url     : https://prove2.me/theorems/0e6d6f19-1bab-481b-ac81-0a3017bcedf0
-- title:
--   Interval replay for every bounded integer draw
-- statement:
--   Write $D_{T,v,c}(\omega)$ for the value and final cursor of the bounded integer sampler on Boolean tape $\omega$, with at most $T$ trials, range $\{0,\ldots,v-1\}$, and initial cursor $c$. A successful result is denoted $(a,s)$ and failure has value $\bot$. For all natural $T,v,c$ and every tape $\omega$, write $D_{T,v,c}(\omega)=(u,s)$, allowing $u=\bot$. Then
--
--   $$c\le s,\qquad
--   \bigl[\forall i\in[c,s),\ \omega'(i)=\omega(i)\bigr]
--   \Longrightarrow D_{T,v,c}(\omega')=(u,s).$$
--
--   The full result, including failure and the final cursor, depends only on the consumed bits. No randomness assumption is needed, and zero or singleton ranges are included.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/BoundedUniformReplay.lean#L54-L110

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
Deterministic locality of bounded rejection sampling. The cursor increases
monotonically, and agreement on the bits actually consumed determines the
whole value, including a rejected draw. No fair-bit law is assumed here.
-/

namespace CountingMatroid.Analysis.BoundedUniformReplay
end CountingMatroid.Analysis.BoundedUniformReplay
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.BoundedUniformReplay
open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program

theorem CountingMatroid.Analysis.BoundedUniformReplay.boundedUniform_interval_replay (trials v start : ℕ) :
    IntervalReplay (fun tape => (boundedUniform tape trials v start).val)
      Prod.snd start := by sorry
