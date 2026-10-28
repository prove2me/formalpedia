-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_TraceReturnIntervalReplay_traceReturn_success_interval
-- name    : CountingMatroid.Analysis.TraceReturnIntervalReplay.traceReturn_success_interval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:57:06.585299+00:00
-- url     : https://prove2.me/theorems/3d591b08-1ae3-44e4-aac8-d61e0fc1c019
-- title:
--   Successful capped return traces replay on their consumed interval
-- statement:
--   Let $n,r\in\mathbb N$, let $o_1,o_2$ be arbitrary Boolean independence-query functions on subsets of $[n]$, let $s$ be any annealing schedule, let $q\in\mathbb Q$, and let $w$ assign rational multipliers to distinct ordered defect indices. A restart cursor $v$ consists of a paired state, tape position $c(v)$, and attempt count. The procedure $R(t,v)$ is the optional returned value of the capped positive-time return trace on Boolean tape $t$, using $s,q,w$ and the program’s chain steps and state classifier. For any initial cursor $v$, any tape $t$, and any successful output $v'$, one has
--   $$R(t,v)=v'\Longrightarrow c(v)\le c(v'),$$
--   and for every other tape $u$,
--   $$\bigl(\forall i\in[c(v),c(v')),\ t(i)=u(i)\bigr)\Longrightarrow R(u,v)=v'.$$
--   The entire successful output is determined by the tape interval consumed by that execution.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/TraceReturnIntervalReplay.lean#L27-L170

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

namespace CountingMatroid.Analysis.TraceReturnIntervalReplay
end CountingMatroid.Analysis.TraceReturnIntervalReplay
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
set_option autoImplicit false

/-!
Capped return scans replay from the interval consumed by their successful
underlying chain attempts. The induction retains the return flag, the abort
state, and early termination of the charged foldlWhile scan.
-/

namespace CountingMatroid.Analysis.TraceReturnIntervalReplay
end CountingMatroid.Analysis.TraceReturnIntervalReplay
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.TraceReturnIntervalReplay
open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.ChainStepIntervalReplay

theorem CountingMatroid.Analysis.TraceReturnIntervalReplay.traceReturn_success_interval {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (s : AnnealingSchedule) (q : ℚ)
    (weights : Multipliers n) (start : RestartCursor n) :
    SuccessReplay (fun tape => (traceReturn r o₁ o₂ tape s q weights start).val)
      RestartCursor.bitCursor start.bitCursor := by sorry
