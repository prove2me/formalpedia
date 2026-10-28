-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_SuccessfulPhaseReplay_successful_history_replay_of_phase_replay
-- name    : CountingMatroid.Analysis.SuccessfulPhaseReplay.successful_history_replay_of_phase_replay
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:14:15.393397+00:00
-- url     : https://prove2.me/theorems/81988457-9666-4558-a587-6fd9ec253076
-- title:
--   Successful phase histories replay from their consumed tape prefix
-- statement:
--   Let $n,r\in\mathbb N$, let $o_1,o_2$ be arbitrary Boolean independence-query functions on subsets of $[n]$, and let $s$ be any annealing schedule. A tape is a function $t:\mathbb N\to\{0,1\}$. A phase cursor stores learned tables, current multipliers, a product accumulator, and a tape position $c(v)$. Write $F_a(t,v)$ for the optional returned value of bounded phase $a$, and $H_j(t)$ for the optional cursor after $j$ phases from the prescribed initialized cursor. Assume every successful phase has interval replay: if $F_a(t,v)=v'$, then $c(v)\le c(v')$, and any tape agreeing with $t$ at all positions in $[c(v),c(v'))$ gives the same returned cursor $v'$. Then, for every $j$, tapes $t_A,t_B$, and cursor $v$,
--   $$H_j(t_A)=v\ \wedge\ \bigl(\forall i<c(v),\ t_A(i)=t_B(i)\bigr)\Longrightarrow H_j(t_B)=v.$$
--   Thus the consumed prefix determines a successful initialized history, provided each phase satisfies the stated interval-replay hypothesis.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/SuccessfulPhaseReplay.lean#L17-L51

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
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhase
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseHistory
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_TransversalPartition
import Definitions.Def_CountingMatroid_Analysis_TransversalProjection
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
import Mathlib.Analysis.Complex.ExponentialBounds
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

namespace CountingMatroid.Analysis.SuccessfulPhaseReplay
end CountingMatroid.Analysis.SuccessfulPhaseReplay
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
set_option autoImplicit false

/-!
History replay from a deterministic single-phase interval invariant. This
module proves the history induction; it asserts no unproved operational
property of the actual phase. The consuming lower-tail theorem must prove
its phase invariant locally. The monotonicity component is essential: it
allows final-prefix agreement to restrict to every earlier consumed prefix.
-/

namespace CountingMatroid.Analysis.SuccessfulPhaseReplay
end CountingMatroid.Analysis.SuccessfulPhaseReplay
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.SuccessfulPhaseReplay

open CountingMatroid.Model

theorem CountingMatroid.Analysis.SuccessfulPhaseReplay.successful_history_replay_of_phase_replay {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (s : AnnealingSchedule)
    (hphase : ∀ a (tape : ℕ → Bool) (previous next : CountingMatroid.Program.AnnealingCursor n),
      (BoundedRunPhase.boundedRunPhase r o₁ o₂ tape s a (some previous)).val = some next →
      previous.bitCursor ≤ next.bitCursor ∧
        ∀ otherTape : ℕ → Bool,
          (∀ i, previous.bitCursor ≤ i → i < next.bitCursor → tape i = otherTape i) →
          (BoundedRunPhase.boundedRunPhase r o₁ o₂ otherTape s a (some previous)).val = some next)
    (tapeA : ℕ → Bool) (j : ℕ) (current : CountingMatroid.Program.AnnealingCursor n)
    (hhistory : BoundedRunPhaseHistory.phaseHistory r o₁ o₂ tapeA s j = some current)
    (tapeB : ℕ → Bool)
    (hagree : ∀ i < current.bitCursor, tapeA i = tapeB i) :
    BoundedRunPhaseHistory.phaseHistory r o₁ o₂ tapeB s j = some current := by sorry
