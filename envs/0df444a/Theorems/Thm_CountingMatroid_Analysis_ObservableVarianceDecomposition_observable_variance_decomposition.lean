-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_ObservableVarianceDecomposition_observable_variance_decomposition
-- name    : CountingMatroid.Analysis.ObservableVarianceDecomposition.observable_variance_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:03:23.245331+00:00
-- url     : https://prove2.me/theorems/0ab177d3-bd1f-4178-9585-f741cce7a3f4
-- title:
--   Variance decomposition for the observable projection
-- statement:
--   Let $n,r\in\mathbb N$ and let $o_1,o_2$ be arbitrary Boolean functions on subset queries of $\{0,\ldots,n-1\}$. On the subsets $S$ of the paired ground $\{0,\ldots,n-1\}\times\{0,1\}$, let $\kappa(S)$ be the program's classifier, whose labels are transversal, defect $(i,k)$, and invalid. A transversal contains one member of every pair; a defect has one empty pair $i$ and one full pair $k$. For $X=\{i:(i,0)\in S\}$ and $Y=\{i:(i,1)\in S\}$, write $g_a(A)$ for the size returned by the greedy scan of $A$ using oracle $o_a$: labels are considered in increasing order and inserted precisely when the oracle accepts the enlarged set. Set $R(S)=\max(g_1(X)+|Y|+g_2(E\setminus Y)-r,0)$, where $E=\{0,\ldots,n-1\}$, and $d(S)=\max(n-R(S),0)$. For rational $q>0$ and rational multipliers $w_{ik}>0$ for distinct $i,k$, let $\pi$ be the normalized operational weights: $q^{d(S)}$ on transversals, $w_{ik}q^{d(S)}$ on defect $(i,k)$, and zero on invalid states. The diagonal defect labels also have zero weight. For a finite probability law $\pi$, the observable projection $P_\pi H$ keeps $H$ on transversals, replaces it on each defect class by its $\pi$-weighted mean, and is zero on invalid states. A class of zero mass has mean zero. Let $H$ be any real function on paired subsets and let $c\in\mathbb R$. For a label $a$, define $m_a=\sum_{\kappa(S)=a}\pi(S)$ and $\mu_a=m_a^{-1}\sum_{\kappa(S)=a}\pi(S)H(S)$, setting $\mu_a=0$ when $m_a=0$. With $\operatorname{Var}_\pi(F)=\sum_S\pi(S)(F(S)-\sum_U\pi(U)F(U))^2$, $$\operatorname{Var}_\pi(P_\pi H)\le\sum_{\kappa(S)=T}\pi(S)(H(S)-c)^2+\sum_{i,k}m_{D_{ik}}(\mu_{D_{ik}}-c)^2.$$
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ObservableVarianceDecomposition.lean#L153-L205

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
import Definitions.Def_CountingMatroidSupport_MarkovChains_Chains_Metropolis
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_Dirichlet
import Definitions.Def_CountingMatroidSupport_Probability_Bilinear
import Definitions.Def_CountingMatroidSupport_Probability_FinDist
import Definitions.Def_CountingMatroidSupport_Probability_FinDistFunctional
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
import Definitions.Def_CountingMatroid_Analysis_IdealExchangeChain
import Definitions.Def_CountingMatroid_Analysis_ObservableProjection
import Definitions.Def_CountingMatroid_Analysis_ObservableVarianceDecomposition
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
import Mathlib.Algebra.QuadraticDiscriminant
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

namespace Arlib
end Arlib
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

/-!
Weighted moments for the operational classifier, and the first inequality
in the paper's observable Poincare proof. These identities do not assert
the quantitative transversal variance or defect transport estimates.
-/

namespace CountingMatroid.Analysis.ObservableVarianceDecomposition
end CountingMatroid.Analysis.ObservableVarianceDecomposition
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ObservableVarianceDecomposition

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.IdealExchangeChain
open CountingMatroid.Analysis.ObservableProjection
open Arlib.Probability Arlib.Probability.FinDist

theorem CountingMatroid.Analysis.ObservableVarianceDecomposition.observable_variance_decomposition {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (w : Multipliers n)
    (hq : 0 < q) (hw : ∀ index, 0 < w index)
    (H : PairedSet n → ℝ) (c : ℝ) :
    let π := operationalLaw r o₁ o₂ q w hq hw
    Var π (observableProjection π H) ≤
      (∑ state : PairedSet n,
        if (classifyState state).val = .transversal then
          π state * (H state - c) ^ 2 else 0) +
      ∑ i : Fin n, ∑ k : Fin n,
        classMass π (.defect i k) * (classMean π H (.defect i k) - c) ^ 2 := by sorry
