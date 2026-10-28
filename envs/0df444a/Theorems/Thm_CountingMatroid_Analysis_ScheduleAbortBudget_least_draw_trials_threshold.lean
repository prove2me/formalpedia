-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_ScheduleAbortBudget_least_draw_trials_threshold
-- name    : CountingMatroid.Analysis.ScheduleAbortBudget.least_draw_trials_threshold
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:14:11.071203+00:00
-- url     : https://prove2.me/theorems/0d3d8b58-4f47-4535-b851-a9d35f688c88
-- title:
--   The bounded doubling search reaches the draw-trial threshold
-- statement:
--   For every requested draw budget $M\in\mathbb N$, let $D$ be the value returned by the schedule's bounded draw-trial search. It begins at exponent $1$ and power $2$, doubles the power while it is below $32M$, and allows $\lfloor\log_2 M\rfloor+8$ iterations, with $\log_2 0=0$. Then $$32M\le 2^D.$$ This includes $M=0$.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ScheduleAbortBudget.lean#L66-L88

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
import Definitions.Def_CountingMatroid_Analysis_ScheduleAbortBudget
import Definitions.Def_CountingMatroid_Interface_Pseudocode
import Definitions.Def_CountingMatroid_Interface_Pseudocode_Extension1
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

namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
set_option autoImplicit false

/-!
The concrete doubling search meets the capped-draw probability threshold.
The schedule budget combines its per-phase draw terms with the restart-tail
term. These are deterministic numerical bounds; operational event bounds
are supplied separately by the conditional abort modules.
-/

namespace CountingMatroid.Analysis.ScheduleAbortBudget
end CountingMatroid.Analysis.ScheduleAbortBudget
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ScheduleAbortBudget

open CountingMatroid.Model CountingMatroid.Model.Operations
open Arlib.Computation (Charged)

theorem CountingMatroid.Analysis.ScheduleAbortBudget.least_draw_trials_threshold (M : ℕ) :
    32 * M ≤ 2 ^ (CountingMatroid.Program.leastDrawTrials M).val := by sorry
