-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_TransversalPartition_transversal_partition_contamination
-- name    : CountingMatroid.Analysis.TransversalPartition.transversal_partition_contamination
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:03:32.214916+00:00
-- url     : https://prove2.me/theorems/36d0752d-79cc-465e-a7d6-f15e0ed51b4f
-- title:
--   The final transversal partition approximates the common-base count
-- statement:
--   Let $n,r\in\mathbb N$ and let $M_1,M_2$ be matroids on $[n]$ whose ground sets are all of $[n]$ and whose ranks both equal $r$. Let $o_1,o_2$ be exact independence oracles for the respective matroids. Let $p=(\varepsilon,\delta)\in\mathbb Q^2$ satisfy $0<\varepsilon,\delta<1$, and assume the number $B$ of subsets that are bases of both matroids is positive. Let $s=\operatorname{setup}(n,p)$, with annealing factor $\rho$ and phase count $L$. For $A\subseteq[n]$, let $T(A)$ select label zero on $A$ and label one on its complement, and define
--   $$C(q)=\sum_{A\subseteq[n]}q^{\,n-\operatorname{pairedRank}(r,o_1,o_2,T(A))},$$
--   where subtraction is truncated in the natural numbers. At the final schedule parameter,
--   $$B\le C(\rho^L)\le(1+\varepsilon/10)B.$$
--   Thus the residual contribution of non-base transversals is at most $\varepsilon B/10$.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/TransversalPartition.lean#L115-L307

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
set_option maxHeartbeats 1000000

namespace CountingMatroid.Analysis.TransversalPartition
end CountingMatroid.Analysis.TransversalPartition
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.TransversalPartition

open CountingMatroid.Model

theorem CountingMatroid.Analysis.TransversalPartition.transversal_partition_contamination (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂)
    (hpositive : 0 < commonBaseCount M₁ M₂) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let c := partitionSum r o₁ o₂ (s.ρ ^ s.L)
    (commonBaseCount M₁ M₂ : ℚ) ≤ c ∧
      c ≤ (1 + p.ε / 10) * (commonBaseCount M₁ M₂ : ℚ) := by sorry
