-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_DefectTransportTwoPairs_defect_transport_two_pairs
-- name    : CountingMatroid.Analysis.DefectTransportTwoPairs.defect_transport_two_pairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T14:53:42.651378+00:00
-- url     : https://prove2.me/theorems/7343237c-22bc-4a8c-95c8-3d3b2acfb16a
-- title:
--   With two pairs the defect-to-event flow uses one edge
-- statement:
--   Let $n,r\in\mathbb N$, $I=\{0,\ldots,n-1\}$, $E=I\times\{0,1\}$, and $\Omega=\mathcal P(E)$. Let $o_1,o_2$ be Boolean oracles on subsets of $I$. Write $R(S)$ for the natural-number value of the paired-rank routine with parameter $r$ and these oracles, and $d(S)=n-R(S)$ with subtraction truncated at zero. A transversal selects one label from each pair; let $T$ be this class. For distinct $i,k\in I$, let $D_{ik}$ be the class having pair $i$ empty, pair $k$ full, and every other pair singly occupied. All other states are invalid. For $q>0$ and positive rational multipliers $w_{ik}$, define $C(q)=\sum_{S\in T}q^{d(S)}$, $D_{ik}(q)=\sum_{S\in D_{ik}}q^{d(S)}$, and $\lambda(S)=q^{d(S)}$ on $T$, $\lambda(S)=w_{ik}q^{d(S)}$ on $D_{ik}$, and $\lambda(S)=0$ on invalid states. Let $Z_w=\sum_S\lambda(S)$ and $\pi(S)=\lambda(S)/Z_w$. For $n>0$, let $Q(S,U)$ be the probability that swapping two independently uniform labels of $E$ sends $S$ to $U$. Let $P$ be its Metropolis kernel with target $\pi$, and set $\kappa(S,U)=Q(S,U)\min(\pi(S),\pi(U))$. Write $\mathcal E_\kappa(H)=\frac12\sum_{S,U}\kappa(S,U)(H(S)-H(U))^2$. For distinct $i,k\in I$ and $a,b\in\{0,1\}$, let $A_{ik}^{ab}$ consist of transversals for which $\mathbf1_{(i,0)\in S}=a$ and $\mathbf1_{(k,0)\in S}=b$. Write $p_T=\pi(T)$, $p_D=\pi(D_{ik})$, and $p_A=\pi(A_{ik}^{ab})$. A flow for these two classes is an antisymmetric real current $J(S,U)$, zero wherever $\kappa(S,U)=0$, with divergence $\sum_UJ(S,U)=\pi(S)\mathbf1_{S\in D_{ik}}/p_D-\pi(S)\mathbf1_{S\in A_{ik}^{ab}}/p_A$. Its energy is $\mathcal F_\kappa(J)=\frac12\sum_{S,U}J(S,U)^2/\kappa(S,U)$, using total real division $x/0=0$. Specialize to $n=2$. For any distinct $i,k$ and bits $a,b$ with $p_A>0$, there is such a flow with $$\mathcal F_\kappa(J)\le8\left(\frac1{p_D}+\frac1{p_A}\right).$$
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/DefectTransportTwoPairs.lean#L96-L163

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
import Definitions.Def_CountingMatroid_Analysis_ExchangeFlowEnergy
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
import Definitions.Def_CountingMatroid_Analysis_TransversalEventMean
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

namespace CountingMatroid.Analysis.DefectTransportTwoPairs
end CountingMatroid.Analysis.DefectTransportTwoPairs
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
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-!
The no-ordinary-slot case of the paper's transport construction. With two
original pairs, an ordered defect fiber and a prescribed transversal event
are singleton states joined by one exchange. The certified unit current
has energy bounded by the sum of the two reciprocal conditional masses.
-/

namespace CountingMatroid.Analysis.DefectTransportTwoPairs
end CountingMatroid.Analysis.DefectTransportTwoPairs
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.DefectTransportTwoPairs

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.IdealExchangeChain
open CountingMatroid.Analysis.ObservableVarianceDecomposition
open CountingMatroid.Analysis.TransversalEventMean
open CountingMatroid.Analysis.ExchangeFlowEnergy

theorem CountingMatroid.Analysis.DefectTransportTwoPairs.defect_transport_two_pairs (r : ℕ) (o₁ o₂ : IndependenceOracle 2)
    (q : ℚ) (w : Multipliers 2) (hn : 0 < 2) (hq : 0 < q)
    (hw : ∀ index, 0 < w index) (i k : Fin 2) (hik : i ≠ k) (a b : Bool)
    (hA : 0 < eventMass (operationalLaw r o₁ o₂ q w hq hw) (pairEvent i k a b)) :
    let π := operationalLaw r o₁ o₂ q w hq hw
    let κ := fun state next : PairedSet 2 =>
      exchangeProposal 2 hn state next * min (π state) (π next)
    ∃ flow : FlowCertificate κ
        (conditionalMeanDemand π (.defect i k) (pairEvent i k a b)),
      flowEnergy κ flow.current ≤ 8 *
        (1 / classMass π (.defect i k) + 1 / eventMass π (pairEvent i k a b)) := by sorry
