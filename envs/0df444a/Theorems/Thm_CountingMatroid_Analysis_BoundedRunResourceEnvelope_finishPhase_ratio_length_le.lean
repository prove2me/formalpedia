-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_BoundedRunResourceEnvelope_finishPhase_ratio_length_le
-- name    : CountingMatroid.Analysis.BoundedRunResourceEnvelope.finishPhase_ratio_length_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T11:48:21.942511+00:00
-- url     : https://prove2.me/theorems/aef68303-7939-460b-aafb-4c177dcf39d7
-- title:
--   Encoding length of the phase ratio
-- statement:
--   For a reduced rational $a=u/v$ with $v>0$, put $\ell(a)=2+(\log_2|u|+1)+(\log_2v+1)$, using floor natural logarithms and $\log_2 0=0$. Let $n,j\in\mathbb N$, let $s$ be any annealing schedule with sample cap $N=s.\mathrm{observations}$, let $w$ assign rational multipliers to distinct ordered pairs in $[n]$, and let $o$ be any observation cursor. Write $u=o.\mathrm{numeratorSum}$ and $c_0=o.\mathrm{counts}(\mathrm{transversal})$. Assume $c_0\le N$. If finishing phase $j$ succeeds with rational ratio $R$ and next multiplier table $w'$, then
--   $$\ell(R)\le\ell(u)+3(N+4).$$
--   This estimates the ratio produced by the finishing routine without requiring that $o$ came from an actual observation loop.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/PhaseResourcePrimitives.lean#L315-L351

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Dict
import Definitions.Def_CountingMatroidSupport_Computation_Heap
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Num
import Definitions.Def_CountingMatroidSupport_Computation_Queue
import Definitions.Def_CountingMatroidSupport_Computation_Rand
import Definitions.Def_CountingMatroidSupport_Computation_Roster
import Definitions.Def_CountingMatroidSupport_Computation_Slot
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroidSupport_Computation_Std
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Program
import Definitions.Def_CountingMatroid_Model_Run
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
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF

set_option autoImplicit false

namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope
end CountingMatroid.Analysis.BoundedRunResourceEnvelope
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.BoundedRunResourceEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines
open CountingMatroid.Analysis.RationalHeight

theorem CountingMatroid.Analysis.BoundedRunResourceEnvelope.finishPhase_ratio_length_le {n : ℕ} (s : AnnealingSchedule) (j : ℕ)
    (weights : Multipliers n) (observed : CountingMatroid.Program.ObservationCursor n)
    (hc : observed.counts .transversal ≤ s.observations)
    (ratio : ℚ) (nextWeights : Multipliers n)
    (h : (CountingMatroid.Program.finishPhase s j weights observed).val =
      some (ratio, nextWeights)) :
    binaryRatLength ratio ≤ binaryRatLength observed.numeratorSum +
      3 * (s.observations + 4) := by sorry
