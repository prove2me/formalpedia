-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_TypeMassLowerBounds_good_type_mass_bounds
-- name    : CountingMatroid.Analysis.TypeMassLowerBounds.good_type_mass_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:33:00.651292+00:00
-- url     : https://prove2.me/theorems/a57f1d30-51c2-4a6e-af65-61d26a9cbe8e
-- title:
--   Factor-four multipliers give polynomial lower bounds on type masses
-- statement:
--   Let $n,r\in\mathbb N$ and let $o_1,o_2$ be arbitrary Boolean independence-query functions on subsets of $[n]=\{0,\ldots,n-1\}$. Paired states are subsets of $[n]\times\{0,1\}$. A transversal selects exactly one label in each pair; a defect $(i,k)$ has empty pair $i$, full pair $k$, and one label at every other pair, with $i\ne k$. Define $d(S)=n-\operatorname{pairedRank}(r,o_1,o_2,S)$ using truncated natural subtraction and the program’s rank scans. Put
--   $$T(A)=\{(i,0):i\in A\}\cup\{(i,1):i\notin A\},\qquad C(q)=\sum_{A\subseteq[n]}q^{d(T(A))},$$
--   and let $D_{ik}(q)$ be the sum of $q^{d(S)}$ over defect $(i,k)$ states. For rational multipliers $w_{ik}$, give a transversal operational weight $q^{d(S)}$, a defect weight $w_{ik}q^{d(S)}$, and every invalid state weight zero. Let $Z(q,w)$ be the sum of these weights over all paired states, and let $m_0(q,w),m_{ik}(q,w)$ be the corresponding class-weight sums divided by $Z(q,w)$. For $\rho\in\mathbb Q$, define $m_U(q,\rho,w)$ as the normalized weighted mean of $\rho^{d(S)}$ on transversals and zero elsewhere.
--   Assume $n>0$, $q>0$, and for every distinct ordered pair $(i,k)$,
--   $$\frac{C(q)}{4D_{ik}(q)}\le w_{ik}\le\frac{4C(q)}{D_{ik}(q)}.$$
--   Then
--   $$Z(q,w)\le5n^2C(q),\qquad m_0(q,w)\ge\frac1{5n^2},\qquad m_{ik}(q,w)\ge\frac1{20n^2}\quad(i\ne k).$$
--   Thus every existing valid type has an inverse-polynomial fraction of the normalized operational weight.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/TypeMassLowerBounds.lean#L73-L138

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
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseHistory
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseWork
import Definitions.Def_CountingMatroid_Analysis_DefectPartitionPositive
import Definitions.Def_CountingMatroid_Analysis_EmpiricalPhaseCertificate
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseEmpiricalUpdate
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseWork
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_ObservePhaseWork
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseMeanCertificate
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
import Definitions.Def_CountingMatroid_Analysis_StationaryMeanIdentities
import Definitions.Def_CountingMatroid_Analysis_TransversalClassPartition
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

namespace CountingMatroid.Analysis.TypeMassLowerBounds
end CountingMatroid.Analysis.TypeMassLowerBounds
namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope
end CountingMatroid.Analysis.BoundedRunResourceEnvelope
namespace CountingMatroid.Analysis.BoundedRunOtherSteps
end CountingMatroid.Analysis.BoundedRunOtherSteps
namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
namespace CountingMatroid.Analysis.LeastHalvingsCost
end CountingMatroid.Analysis.LeastHalvingsCost
namespace CountingMatroid.Analysis
end CountingMatroid.Analysis
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.RestartPhaseWork
end CountingMatroid.Analysis.RestartPhaseWork
namespace CountingMatroid.Analysis.BoundedRunPhase
end CountingMatroid.Analysis.BoundedRunPhase
namespace CountingMatroid.Analysis.FinishPhaseWeightsSize
end CountingMatroid.Analysis.FinishPhaseWeightsSize
namespace CountingMatroid.Analysis.BoundedRunOracleCalls
end CountingMatroid.Analysis.BoundedRunOracleCalls
namespace CountingMatroid.Analysis.ResourceBound
end CountingMatroid.Analysis.ResourceBound
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
set_option autoImplicit false

namespace CountingMatroid.Analysis.TypeMassLowerBounds
end CountingMatroid.Analysis.TypeMassLowerBounds
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.TypeMassLowerBounds

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.StationaryMeanIdentities

theorem CountingMatroid.Analysis.TypeMassLowerBounds.good_type_mass_bounds {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (w : Multipliers n)
    (hn : 0 < n) (hq : 0 < q)
    (hgood : ∀ index,
      (TransversalPartition.partitionSum r o₁ o₂ q /
        FirstPhaseFailure.defectPartition r o₁ o₂ q index) / 4 ≤ w index ∧
      w index ≤ 4 * (TransversalPartition.partitionSum r o₁ o₂ q /
        FirstPhaseFailure.defectPartition r o₁ o₂ q index)) :
    normalizer r o₁ o₂ q w ≤
      5 * (n : ℚ) ^ 2 * TransversalPartition.partitionSum r o₁ o₂ q ∧
    1 / (5 * (n : ℚ) ^ 2) ≤ typeMean r o₁ o₂ q w .transversal ∧
    ∀ index : DefectIndex n, 1 / (20 * (n : ℚ) ^ 2) ≤
      typeMean r o₁ o₂ q w (.defect index.emptyPair index.fullPair) := by sorry
