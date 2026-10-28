-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_ConditionalDefectCoefficients_transversal_total_pos
-- name    : CountingMatroid.Analysis.ConditionalDefectCoefficients.transversal_total_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T14:57:31.291982+00:00
-- url     : https://prove2.me/theorems/3bc158b5-d597-484c-9530-e3393a74a187
-- title:
--   Every conditional transversal partition sum is positive
-- statement:
--   Let $n,r\in\mathbb N$, let $o_1,o_2:\{0,1\}^n\to\{0,1\}$ be fixed Boolean oracle functions, and let $q\in\mathbb Q$ satisfy $q>0$. A partial assignment $\sigma:[n]\to\{\bot,0,1\}$ specifies one chosen member at some paired indices. A subset $A\subseteq[n]$ respects $\sigma$ when every assignment of zero requires membership in $A$, and every assignment of one requires nonmembership. Let $d(A)$ be $n$ minus the value of the operational paired-rank routine on the transversal $\{(i,\mathbf1_{i\notin A}):i\in[n]\}$, using truncated natural subtraction. Then, for every partial assignment,
--
--   $$C_\sigma(q):=\sum_{\substack{A\subseteq[n]\\A\text{ respects }\sigma}}q^{d(A)}>0.$$
--
--   This supplies positivity of conditional normalizing sums without needing an exact-oracle promise.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ConditionalDefectCoefficients.lean#L82-L104

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
import Definitions.Def_CountingMatroid_Analysis_ConditionalDefectCoefficients
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_InitialMultipliersGood
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
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.List
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
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
set_option autoImplicit false

/-!
Conditional transversal and defect totals for the operational rank weights.
The empty assignment recovers the existing partition sums. Positivity and
binary splitting below concern these finite sums; the quadratic signature
inequalities are separate mathematical obligations.
-/

namespace CountingMatroid.Analysis.ConditionalDefectCoefficients
end CountingMatroid.Analysis.ConditionalDefectCoefficients
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ConditionalDefectCoefficients

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.TransversalPartition

theorem CountingMatroid.Analysis.ConditionalDefectCoefficients.transversal_total_pos {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (hq : 0 < q) (σ : Assignment n) :
    0 < transversalTotal r o₁ o₂ q σ := by sorry
