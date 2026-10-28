-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_AnnealingPartitionDrift_partition_step_bounds
-- name    : CountingMatroid.Analysis.AnnealingPartitionDrift.partition_step_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T14:11:11.855462+00:00
-- url     : https://prove2.me/theorems/7ec41c03-f5c3-4f6c-bc43-b4d848b3cc1d
-- title:
--   Factor-two drift of transversal and defect partition sums
-- statement:
--   Let $n\ge1$, $r\in\mathbb N$, and let $o_1,o_2$ be arbitrary Boolean subset oracles. Let $p=(\varepsilon,\delta)$ consist of rational accuracy and confidence parameters with $0<\varepsilon<1$ and $0<\delta<1$. Let $\rho$ be the setup cooling factor. For a paired subset $X\subseteq[n]\times\{0,1\}$, let $d(X)=\max(n-R(X),0)$, where $R(X)$ is the value of the program’s paired-rank scan with parameter $r$ and these oracles. A transversal $X_A$ chooses $(i,0)$ for $i\in A$ and $(i,1)$ otherwise. Define $$C_j=\sum_{A\subseteq[n]}(\rho^j)^{d(X_A)},\qquad D_j(e,f)=\sum_{X:\,\mathrm{classify}(X)=\mathrm{defect}(e,f)}(\rho^j)^{d(X)},$$ where $(e,f)$ is any ordered pair of distinct indices, and the defect class has empty pair $e$ and full pair $f$. For every $j\in\mathbb N$, $$0<C_j,\qquad \frac{C_j}{2}\le C_{j+1}\le C_j,$$ and $$0\le D_j(e,f),\qquad \frac{D_j(e,f)}2\le D_{j+1}(e,f)\le D_j(e,f).$$ These inequalities control cooling for every fixed class, including empty defect classes.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/AnnealingPartitionDrift.lean#L90-L123

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
import Definitions.Def_CountingMatroid_Analysis_AnnealingPartitionDrift
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhase
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
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
import Mathlib.Algebra.Order.Ring.Pow
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

namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
set_option autoImplicit false

namespace CountingMatroid.Analysis.AnnealingPartitionDrift
end CountingMatroid.Analysis.AnnealingPartitionDrift
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.AnnealingPartitionDrift

open CountingMatroid.Model

theorem CountingMatroid.Analysis.AnnealingPartitionDrift.partition_step_bounds (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (j : ℕ) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let C := fun a => TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ a)
    let D := fun a index => FirstPhaseFailure.defectPartition r o₁ o₂ (s.ρ ^ a) index
    0 < C j ∧ C j / 2 ≤ C (j + 1) ∧ C (j + 1) ≤ C j ∧
      ∀ index, 0 ≤ D j index ∧
        D j index / 2 ≤ D (j + 1) index ∧ D (j + 1) index ≤ D j index := by sorry
