-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_DefectSlotBudget_defect_slot_budget
-- name    : CountingMatroid.Analysis.DefectSlotBudget.defect_slot_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:09:28.651098+00:00
-- url     : https://prove2.me/theorems/4f498617-5087-4920-8110-ac0b99d35f61
-- title:
--   The two-hole slot budget is bounded by normalized defect partitions
-- statement:
--   Let $n,r\in\mathbb N$, $I=\{0,\ldots,n-1\}$, $E=I\times\{0,1\}$, and $\Omega=\mathcal P(E)$. Let $o_1,o_2$ be Boolean oracles on subsets of $I$. Write $R(S)$ for the natural-number value of the paired-rank routine with parameter $r$ and these oracles, and $d(S)=n-R(S)$ with subtraction truncated at zero. A transversal selects one label from each pair; let $T$ be this class. For distinct $i,k\in I$, let $D_{ik}$ be the class having pair $i$ empty, pair $k$ full, and every other pair singly occupied. All other states are invalid. For $q>0$ and positive rational multipliers $w_{ik}$, define $C(q)=\sum_{S\in T}q^{d(S)}$, $D_{ik}(q)=\sum_{S\in D_{ik}}q^{d(S)}$, and $\lambda(S)=q^{d(S)}$ on $T$, $\lambda(S)=w_{ik}q^{d(S)}$ on $D_{ik}$, and $\lambda(S)=0$ on invalid states. Let $Z_w=\sum_S\lambda(S)$ and $\pi(S)=\lambda(S)/Z_w$. For distinct $i,k\in I$ and $a,b\in\{0,1\}$, let $A_{ik}^{ab}$ consist of transversals for which $\mathbf1_{(i,0)\in S}=a$ and $\mathbf1_{(k,0)\in S}=b$. Write $p_T=\pi(T)$, $p_D=\pi(D_{ik})$, and $p_A=\pi(A_{ik}^{ab})$. Assume $p_A>0$. Put $B=\{(k,1-b)\}$, $U=I\setminus\{i,k\}$, $p=(i,1-a)$, $p'=(k,b)$, and $R_0=\{p,p'\}$. For each hole $x$, let $s_x$ be the sum of $q^{d(S)}$ over distinct states $S=B\cup(R_0\setminus\{x\})\cup\{(t,\epsilon_t):t\in U\}$ as the bits $\epsilon_t$ vary. Put $h(p)=1/s_p$, $h(p')=-1/s_{p'}$. Set $W(t,c)=w_{ik}$ if $t=i$, $W(t,c)=1$ if $t=k$, and $W(t,c)=w_{tk}$ otherwise. For $t\in U$, let $V_t(x,x)=0$ and let $V_t(x,y)$ for $x\ne y$ sum the same weights over states $B\cup(R_0\setminus\{x,y\})\cup\{(t,0),(t,1)\}\cup\{(u,\epsilon_u):u\in U\setminus\{t\}\}$. Define $$\Phi=\sum_{x\in R_0}s_xh(x)^2/W(x),\qquad F_t=\sum_{x,y\in R_0}V_t(x,y)h(x)h(y).$$ Then $$2n^2Z_w\left(\Phi-\sum_{t\in U}\frac{F_t}{W(t,0)}\right)\le 2n^2\left(\frac1{p_D}+\frac1{p_A}+\frac2{D_{ik}(q)p_A}\sum_{t\in I\setminus\{i,k\}}\frac{D_{it}(q)}{w_{tk}}\right).$$
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/DefectSlotBudget.lean#L20-L127

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
import Definitions.Def_CountingMatroid_Analysis_BalancedCliqueFlow
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhase
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseHistory
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseWork
import Definitions.Def_CountingMatroid_Analysis_ConditionalDefectCoefficients
import Definitions.Def_CountingMatroid_Analysis_ConditionalDefectExtractionCoefficients
import Definitions.Def_CountingMatroid_Analysis_ConditionalDefectQuadratics
import Definitions.Def_CountingMatroid_Analysis_ConditionalTransversalSlots
import Definitions.Def_CountingMatroid_Analysis_ConditionalTransversalSplitTransport
import Definitions.Def_CountingMatroid_Analysis_ConditionalVarianceTree
import Definitions.Def_CountingMatroid_Analysis_CubicTensorContraction
import Definitions.Def_CountingMatroid_Analysis_DefectPartitionPositive
import Definitions.Def_CountingMatroid_Analysis_DefectPartitionQuadraticConstruction
import Definitions.Def_CountingMatroid_Analysis_DefectSlotConservation
import Definitions.Def_CountingMatroid_Analysis_DefectSlotSplitSignature
import Definitions.Def_CountingMatroid_Analysis_DisjointFlowSum
import Definitions.Def_CountingMatroid_Analysis_EmbeddedFlow
import Definitions.Def_CountingMatroid_Analysis_EmpiricalPhaseCertificate
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_ExchangeFlowEnergy
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseEmpiricalUpdate
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseWork
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_IdealExchangeChain
import Definitions.Def_CountingMatroid_Analysis_InitialMultipliersGood
import Definitions.Def_CountingMatroid_Analysis_LeafCliqueFlow
import Definitions.Def_CountingMatroid_Analysis_LorentzianDirectionalSignature
import Definitions.Def_CountingMatroid_Analysis_ObservableProjection
import Definitions.Def_CountingMatroid_Analysis_ObservableVarianceDecomposition
import Definitions.Def_CountingMatroid_Analysis_ObservePhaseWork
import Definitions.Def_CountingMatroid_Analysis_OmittedRankWeightPolynomial
import Definitions.Def_CountingMatroid_Analysis_OmittedSlotCoefficientFormula
import Definitions.Def_CountingMatroid_Analysis_OmittedSlotQuadratic
import Definitions.Def_CountingMatroid_Analysis_OmittedTutteNormalization
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseMeanCertificate
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Definitions.Def_CountingMatroid_Analysis_RankWeightQuadraticSignature
import Definitions.Def_CountingMatroid_Analysis_RankWeightSupportExchange
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
import Definitions.Def_CountingMatroid_Analysis_SlotBlockSignature
import Definitions.Def_CountingMatroid_Analysis_SlotDemandPairing
import Definitions.Def_CountingMatroid_Analysis_SlotDemandRecursion
import Definitions.Def_CountingMatroid_Analysis_SlotTransportFlow
import Definitions.Def_CountingMatroid_Analysis_SquarefreeCoordinateHessian
import Definitions.Def_CountingMatroid_Analysis_StationaryMeanIdentities
import Definitions.Def_CountingMatroid_Analysis_ThreePairSignatureSchur
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
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Combinatorics.Matroid.Sum
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finsupp.Indicator
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.List
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.MvPolynomial.Homogeneous
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
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.Real.Lemmas

namespace CountingMatroid.Analysis.DefectSlotBudget
end CountingMatroid.Analysis.DefectSlotBudget
namespace CountingMatroid.Analysis.DefectSlotFutureBound
end CountingMatroid.Analysis.DefectSlotFutureBound
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
namespace CountingMatroid.Analysis.SlotLeafGeometry
end CountingMatroid.Analysis.SlotLeafGeometry
namespace CountingMatroid.Analysis.SlotOmissionPatternCharacterization
end CountingMatroid.Analysis.SlotOmissionPatternCharacterization
namespace CountingMatroid.Analysis.TwoLabelDerivativeNilpotence
end CountingMatroid.Analysis.TwoLabelDerivativeNilpotence
namespace CountingMatroid.Analysis.MixedDirectionalRankWeightSignature
end CountingMatroid.Analysis.MixedDirectionalRankWeightSignature
namespace CountingMatroid.Analysis.RankWeightCoordinateLorentzian
end CountingMatroid.Analysis.RankWeightCoordinateLorentzian
namespace CountingMatroid.Analysis.RankWeightCoordinateSignature
end CountingMatroid.Analysis.RankWeightCoordinateSignature
namespace CountingMatroid.Analysis.RankWeightResidualSignature
end CountingMatroid.Analysis.RankWeightResidualSignature
namespace CountingMatroid.Analysis.RankWeightClosurePair
end CountingMatroid.Analysis.RankWeightClosurePair
namespace CountingMatroid.Analysis.ClosureClassQuadraticBound
end CountingMatroid.Analysis.ClosureClassQuadraticBound
namespace CountingMatroid.Analysis.SquarefreeFullDerivative
end CountingMatroid.Analysis.SquarefreeFullDerivative
namespace CountingMatroid.Analysis.BinaryRankWeightSignature
end CountingMatroid.Analysis.BinaryRankWeightSignature
namespace CountingMatroid.Analysis.CubicDirectionalSignature
end CountingMatroid.Analysis.CubicDirectionalSignature
namespace CountingMatroid.Analysis.CubicTensorRayleighContraction
end CountingMatroid.Analysis.CubicTensorRayleighContraction
namespace CountingMatroid.Analysis.NonnegativeContractionLimit
end CountingMatroid.Analysis.NonnegativeContractionLimit
namespace CountingMatroid.Analysis.QuadraticHyperplanePointwiseLimit
end CountingMatroid.Analysis.QuadraticHyperplanePointwiseLimit
namespace CountingMatroid.Analysis.ConnectedRayleighHyperplane
end CountingMatroid.Analysis.ConnectedRayleighHyperplane
namespace CountingMatroid.Analysis.ConnectedNormalizedRayleigh
end CountingMatroid.Analysis.ConnectedNormalizedRayleigh
namespace CountingMatroid.Analysis.ConnectedLaplacianKernel
end CountingMatroid.Analysis.ConnectedLaplacianKernel
namespace CountingMatroid.Analysis.RayleighFixedKernel
end CountingMatroid.Analysis.RayleighFixedKernel
namespace CountingMatroid.Analysis.QuadraticSignatureHyperplane
end CountingMatroid.Analysis.QuadraticSignatureHyperplane
namespace CountingMatroid.Analysis.CubicExchangeCut
end CountingMatroid.Analysis.CubicExchangeCut
namespace CountingMatroid.Analysis.CubicThirdDerivativeSupport
end CountingMatroid.Analysis.CubicThirdDerivativeSupport
namespace CountingMatroid.Analysis.NonnegativeDirectionalMConvexSupport
end CountingMatroid.Analysis.NonnegativeDirectionalMConvexSupport
namespace CountingMatroid.Analysis.LinearSubstitutionHessian
end CountingMatroid.Analysis.LinearSubstitutionHessian
namespace CountingMatroid.Analysis.LinearPolynomialChainRule
end CountingMatroid.Analysis.LinearPolynomialChainRule
namespace CountingMatroid.Analysis.PairedRankValue
end CountingMatroid.Analysis.PairedRankValue
namespace CountingMatroid.Analysis.SignatureOrthogonalNonpositive
end CountingMatroid.Analysis.SignatureOrthogonalNonpositive
namespace CountingMatroid.Analysis.DefectSlotRoot
end CountingMatroid.Analysis.DefectSlotRoot
namespace CountingMatroid.Analysis.ConditionalLeafClassifier
end CountingMatroid.Analysis.ConditionalLeafClassifier
namespace CountingMatroid.Analysis.ExchangeProposalGeometry
end CountingMatroid.Analysis.ExchangeProposalGeometry
namespace CountingMatroid.Analysis.LeafExchangeProposal
end CountingMatroid.Analysis.LeafExchangeProposal
namespace CountingMatroid.Analysis.BalancedCliqueEnergy
end CountingMatroid.Analysis.BalancedCliqueEnergy
namespace CountingMatroid.Analysis.OnePairObservablePoincare
end CountingMatroid.Analysis.OnePairObservablePoincare
set_option autoImplicit false

/-!
Normalize the iterated two-hole potential estimate into the defect/event
mass bound. Root future entries are bounded by full defect partitions.
-/

namespace CountingMatroid.Analysis.DefectSlotBudget
end CountingMatroid.Analysis.DefectSlotBudget
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.DefectSlotBudget

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.IdealExchangeChain
open CountingMatroid.Analysis.ObservableVarianceDecomposition
open CountingMatroid.Analysis.TransversalEventMean
open CountingMatroid.Analysis.DefectSlotSplitSignature
open CountingMatroid.Analysis.SlotDemandRecursion

theorem CountingMatroid.Analysis.DefectSlotBudget.defect_slot_budget {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (w : Multipliers n) (hq : 0 < q) (hw : ∀ index, 0 < w index)
    (i k : Fin n) (hik : i ≠ k) (a b : Bool)
    (hA : 0 < eventMass (operationalLaw r o₁ o₂ q w hq hw) (pairEvent i k a b)) :
    let π := operationalLaw r o₁ o₂ q w hq hw
    let B : PairedSet n := {(k, !b)}
    let U : Finset (Fin n) := (Finset.univ.erase i).erase k
    let p : PairedGround n := (i, !a)
    let d : PairedGround n := (k, b)
    let W : PairedGround n → ℝ := fun hole =>
      if hole.1 = i then (w ⟨i, k, hik⟩ : ℝ)
      else if h : hole.1 = k then 1 else (w ⟨hole.1, k, h⟩ : ℝ)
    let root := twoHoleRoot r o₁ o₂ q B U p d
    let D := FirstPhaseFailure.defectPartition r o₁ o₂ q
    let C : ℝ := (2 * (n : ℝ) ^ 2) * (StationaryMeanIdentities.normalizer r o₁ o₂ q w : ℝ)
    C * (nodePotential r o₁ o₂ q B U W root -
      ∑ t ∈ U, nodeFuture r o₁ o₂ q B U root t / W (t, false)) ≤
        (2 * (n : ℝ) ^ 2) *
          (1 / classMass π (.defect i k) + 1 / eventMass π (pairEvent i k a b) +
            (2 / ((D ⟨i, k, hik⟩ : ℝ) * eventMass π (pairEvent i k a b))) *
              ∑ t : Fin n, if h : t ≠ i ∧ t ≠ k then
                (D ⟨i, t, Ne.symm h.1⟩ : ℝ) / (w ⟨t, k, h.2⟩ : ℝ) else 0) := by sorry
