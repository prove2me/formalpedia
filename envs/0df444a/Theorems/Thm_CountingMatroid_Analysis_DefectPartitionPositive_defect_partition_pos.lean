-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_DefectPartitionPositive_defect_partition_pos
-- name    : CountingMatroid.Analysis.DefectPartitionPositive.defect_partition_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T14:12:52.268203+00:00
-- url     : https://prove2.me/theorems/a4c5941a-fec7-42ad-97fb-9aad2c604b62
-- title:
--   Every ordered-defect partition sum is positive
-- statement:
--   Write $[n]=\{0,\ldots,n-1\}$ and $G=[n]\times\{0,1\}$, with $\bar c=1-c$ for a Boolean label. A paired state is a subset of $G$. A transversal has exactly one label at each pair; an ordered defect $(i,k)$ has pair $i$ empty, pair $k$ doubled, and every other pair singly occupied.
--
--   Fix natural $n,r$, Boolean subset-oracle functions $o_1,o_2$, and a rational parameter $q$. For a paired state $S$, write $\widehat r(S)$ for the value returned by the program's paired-rank routine using $r,o_1,o_2$, and put $f(S)=q^{\,n\mathbin{\dot-}\widehat r(S)}$, with truncated natural subtraction. No correctness promise for the oracles is implicit. Assume $q>0$. For distinct $i,k$, let
--   $$Z_{i,k}=\sum_{\operatorname{classify}(S)=\mathrm{defect}(i,k)}f(S).$$
--   Then
--   $$Z_{i,k}>0.$$
--   Thus the unmultiplied partition sum of every ordered-defect class has a valid positive denominator, even for arbitrary Boolean oracle functions.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/DefectPartitionPositive.lean#L119-L142

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
import Definitions.Def_CountingMatroid_Analysis_DefectPartitionPositive
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

namespace CountingMatroid.Analysis.DefectPartitionPositive
end CountingMatroid.Analysis.DefectPartitionPositive
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.DefectPartitionPositive

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program

theorem CountingMatroid.Analysis.DefectPartitionPositive.defect_partition_pos {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (hq : 0 < q) (index : DefectIndex n) :
    0 < FirstPhaseFailure.defectPartition r o₁ o₂ q index := by sorry
