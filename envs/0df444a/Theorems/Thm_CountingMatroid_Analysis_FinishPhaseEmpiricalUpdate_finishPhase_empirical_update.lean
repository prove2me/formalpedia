-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_FinishPhaseEmpiricalUpdate_finishPhase_empirical_update
-- name    : CountingMatroid.Analysis.FinishPhaseEmpiricalUpdate.finishPhase_empirical_update
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T14:11:06.348414+00:00
-- url     : https://prove2.me/theorems/b657371f-6e0b-49ed-90c5-f4f16ab997a3
-- title:
--   Positive empirical counts give the exact phase-finishing update
-- statement:
--   Let $n\in\mathbb N$, let $s$ be an annealing schedule with observation count $N=s.\mathrm{observations}$ and phase count $L=s.L$, and let $j\in\mathbb N$ be a phase index. Let $w_{ik}\in\mathbb Q$ be multipliers indexed by distinct ordered coordinates $i,k\in[n]$. An observation record contains a paired state, a tape cursor, a natural count $c_\gamma$ for each classifier kind $\gamma$, and a rational numerator sum $u$. Write $c_T$ for its transversal count and $c_{ik}$ for its ordered-defect count.
--
--   Suppose $N>0$, $c_T>0$, and $c_{ik}>0$ for every distinct ordered pair. Then the phase-finishing routine succeeds and returns
--
--   $$\operatorname{finishPhase}(s,j,w,\mathrm{observed}).\mathrm{val}=\operatorname{some}(u/c_T,w'),$$
--   $$w'_{ik}=\begin{cases}w_{ik}c_T/c_{ik},&j+1<L,\\w_{ik},&j+1\ge L.\end{cases}$$
--
--   This deterministic formula uses each original multiplier once. The hypotheses are meaningful even when there are no defect indices, in which case their positivity condition is vacuous.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/FinishPhaseEmpiricalUpdate.lean#L48-L188

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
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseEmpiricalUpdate
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

namespace CountingMatroid.Analysis.FinishPhaseEmpiricalUpdate
end CountingMatroid.Analysis.FinishPhaseEmpiricalUpdate
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.FinishPhaseEmpiricalUpdate

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program

theorem CountingMatroid.Analysis.FinishPhaseEmpiricalUpdate.finishPhase_empirical_update {n : ℕ} (s : AnnealingSchedule) (j : ℕ)
    (weights : Multipliers n) (observed : ObservationCursor n)
    (hN : 0 < s.observations) (hzero : 0 < observed.counts .transversal)
    (hdefect : ∀ index : DefectIndex n,
      0 < observed.counts (.defect index.emptyPair index.fullPair)) :
    (finishPhase s j weights observed).val =
      some (observed.numeratorSum / (observed.counts .transversal : ℚ),
        empiricalWeights s j weights observed) := by sorry
