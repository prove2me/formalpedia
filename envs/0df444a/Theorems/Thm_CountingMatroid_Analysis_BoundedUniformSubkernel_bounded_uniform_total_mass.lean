-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_BoundedUniformSubkernel_bounded_uniform_total_mass
-- name    : CountingMatroid.Analysis.BoundedUniformSubkernel.bounded_uniform_total_mass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:08:54.600903+00:00
-- url     : https://prove2.me/theorems/dff28771-c996-40cf-b25d-51c7b2868788
-- title:
--   Covered successful draws have total mass at most one
-- statement:
--   For a finite Boolean prefix $h$ and $t\in\mathbb N$, write $\mathbb P_{h,t}(E)$ for the fraction of the $2^t$ Boolean suffixes $b$ of length $t$ for which $E$ holds on the tape $h\mathbin{+\!+}b$, extended by zeros beyond its end.
--
--   Write $D_{T,v,c}(\omega)$ for the value and final cursor of the bounded integer sampler on Boolean tape $\omega$, with at most $T$ trials, range $\{0,\ldots,v-1\}$, and initial cursor $c$. A successful result is denoted $(a,s)$ and failure has value $\bot$. For every prefix $h$ and natural $T,v,t$, let $S_a$ be the event of returning $a$ from initial cursor $|h|$ at a final cursor at most $|h|+t$. Then
--
--   $$\sum_{a=0}^{v-1}\mathbb P_{h,t}(S_a)\le1.$$
--
--   The successful law is a subprobability law: failed draws and successes beyond the horizon are not counted. The bound includes the empty range $v=0$.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/BoundedUniformSubkernel.lean#L66-L109

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
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformAbortMass
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformReplay
import Definitions.Def_CountingMatroid_Analysis_ChainStepIntervalReplay
import Definitions.Def_CountingMatroid_Analysis_FiniteStoppedFiberMass
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
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
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Infix
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.List
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
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

namespace CountingMatroid.Analysis.BoundedUniformSubkernel
end CountingMatroid.Analysis.BoundedUniformSubkernel
namespace CountingMatroid.Analysis.BoundedUniformSuccessWords
end CountingMatroid.Analysis.BoundedUniformSuccessWords
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.FiniteObservationMarkov
end CountingMatroid.Analysis.FiniteObservationMarkov
namespace CountingMatroid.Analysis.FiniteTapePrefixBound
end CountingMatroid.Analysis.FiniteTapePrefixBound
namespace CountingMatroid.Analysis.InitialRestartLaw
end CountingMatroid.Analysis.InitialRestartLaw
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! Covered successful bounded draws are subuniform, including the zero-bit
singleton draw. The estimate sums all stopping cursors before composing a
fresh-suffix continuation. -/
namespace CountingMatroid.Analysis.BoundedUniformSubkernel
end CountingMatroid.Analysis.BoundedUniformSubkernel
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.BoundedUniformSubkernel
open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.FiniteStoppedFiberMass
open CountingMatroid.Analysis.BoundedUniformSuccessWords

theorem CountingMatroid.Analysis.BoundedUniformSubkernel.bounded_uniform_total_mass (head : List Bool) (trials v t : ℕ) :
    (∑ a : Fin v, fairMass head t (fun tape => ∃ stop,
      stop ≤ head.length + t ∧
      (boundedUniform tape trials v head.length).val = (some a.val, stop))) ≤ 1 := by sorry
