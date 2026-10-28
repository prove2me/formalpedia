-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_SlotTransportFlow_slot_transport_flow
-- name    : CountingMatroid.Analysis.SlotTransportFlow.slot_transport_flow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:54:49.242192+00:00
-- url     : https://prove2.me/theorems/0fa65fad-2fc5-4a0d-9a6f-82cdaf06c761
-- title:
--   The slot recursion constructs a transport flow with the root energy bound
-- statement:
--   Let $n,r\in\mathbb N$, $I=\{0,\ldots,n-1\}$, and $E=I\times\{0,1\}$. Let $o_1,o_2$ be arbitrary Boolean functions on $n$-bit subset queries and $q\in\mathbb Q$. For $T\subseteq I$, let $g_j(T)$ be the number of accepted elements when scanning $I$ in increasing order, attempting to add each element of $T$ to the current accepted set and accepting precisely when $o_j$ returns true on the candidate subset. For $A\subseteq E$, set $X_A=\{i:(i,0)\in A\}$, $Y_A=\{i:(i,1)\in A\}$, and $\rho(A)=\max(g_1(X_A)+|Y_A|+g_2(I\setminus Y_A)-r,0)$. This is the value of the paired-rank routine. Put $w(A)=q^{\max(n-\rho(A),0)}\in\mathbb R$. For $B,R\subseteq E$, $U\subseteq I$, and $i\in E$, let $\mathcal C(B,R,U;i)$ be the set of distinct states $A=B\cup(R\setminus\{i\})\cup\{(s,\epsilon(s)):s\in U\}$ obtainable from functions $\epsilon:I\to\{0,1\}$, and define $$s(B,R,U;i)=\sum_{A\in\mathcal C(B,R,U;i)}w(A).$$ A demand node $N=(R,h)$ consists of its hole set $R$ and a function $h:E\to\mathbb R$. For a processed slot $t$, its child $N_c=(R_c,h_c)$, $c\in\{0,1\}$, has $R_c=R\cup\{(t,c)\}$, remaining slots $U\setminus\{t\}$, and values equal to $h$ except that $$h_c(t,c)=-\frac{\sum_{i\in R}s(B,R_c,U\setminus\{t\};i)h(i)}{s(B,R_c,U\setminus\{t\};(t,c))}.$$ Division is real division, with $a/0=0$. For an ordered list $L$ of slots, let $\mathcal L_L(N)$ be the list of terminal nodes obtained by processing the slots in order, recursively concatenating the $c=0$ and $c=1$ branches; at each step $U$ is the set of remaining list entries. The empty list returns $N$ itself. Define $V_t(B,R,U;i,i)=0$; for $i\ne j$, define $V_t(B,R,U;i,j)$ as the sum of $w(A)$ over distinct states $$A=B\cup(R\setminus\{i,j\})\cup\{(t,0),(t,1)\}\cup\{(s,\epsilon(s)):s\in U\setminus\{t\}\}.$$ For $W:E\to\mathbb R$, put $$\Phi_{B,U,W}(N)=\sum_{i\in R}\frac{s(B,R,U;i)h(i)^2}{W(i)},\qquad F_t(B,U,N)=\sum_{i,j\in R}V_t(B,R,U;i,j)h(i)h(j).$$ Define the state demand by $$d_{B,U,N}(A)=w(A)\sum_{i\in R:\ A\in\mathcal C(B,R,U;i)}h(i).$$ For a terminal node, write $v_R(i)=B\cup(R\setminus\{i\})$. Suppose $q>0$, the slot list $L$ has no repetitions, $U$ is its set of entries, and $R\ne\varnothing$. Assume $B\cap R=\varnothing$, $(s,c)\notin B\cup R$ for every $s\in U$ and $c\in\{0,1\}$, $|B|+|R|+|U|=n+1$, and the balance equation $\sum_{i\in R}s(B,R,U;i)h(i)=0$. Assume $W(t,0)=W(t,1)>0$ for $t\in U$. Assume the global slot-splitting condition: for every $B',R'\subseteq E$, $U'\subseteq I$ with $B'\cap R'=\varnothing$, $(s,c)\notin B'\cup R'$ for $s\in U'$ and $c\in\{0,1\}$, and $|B'|+|R'|+|U'|=n+1$, and every $t'\in U'$ and $v:E\to\mathbb R$, set $a_i=s(B',R'\cup\{(t',0)\},U'\setminus\{t'\};i)$, $b_i=s(B',R'\cup\{(t',1)\},U'\setminus\{t'\};i)$ and $u=a_{(t',0)}$. Then $$\sum_{i\in R'}(a_i+b_i)v(i)=0\ \Longrightarrow\ \frac{2(\sum_{i\in R'}a_iv(i))^2}{u}\le-\sum_{i,j\in R'}V_{t'}(B',R',U';i,j)v(i)v(j).$$ Let $\kappa:\mathcal P(E)\times\mathcal P(E)\to\mathbb R$ be symmetric and let $C>0$. For every leaf $N'=(R',h')\in\mathcal L_L(N)$, require $W(i)>0$ for $i\in R'$ and, for distinct $x,y\in R'$, $$\min\{W(x)s(B,R',\varnothing;x),W(y)s(B,R',\varnothing;y)\}\le C\kappa(v_{R'}(x),v_{R'}(y)).$$ Then there is a real current $J$ on ordered pairs of states such that $J(A,D)=-J(D,A)$, $\kappa(A,D)=0$ implies $J(A,D)=0$, and $\sum_DJ(A,D)=d_{B,U,N}(A)$ for every state $A$. Its energy satisfies $$\frac12\sum_{A,D\subseteq E}\frac{J(A,D)^2}{\kappa(A,D)}\le C\left(\Phi_{B,U,W}(N)-\sum_{t\in U}\frac{F_t(B,U,N)}{W(t,0)}\right).$$ All divisions are real divisions with $a/0=0$.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/SlotTransportFlow.lean#L59-L172

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
set_option autoImplicit false

/-!
Assemble the balanced binary demand tree into an exchange-supported flow.
The exact first-moment identity cancels ordinary-hole demands, while the
finite-set leaf geometry makes the energies additive. The conductance
hypothesis is local to the terminal cliques and is kept separate from the
operational defect/event specialization.
-/

namespace CountingMatroid.Analysis.SlotTransportFlow
end CountingMatroid.Analysis.SlotTransportFlow
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.SlotTransportFlow

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.ExchangeFlowEnergy
open CountingMatroid.Analysis.DefectSlotSplitSignature
open CountingMatroid.Analysis.SlotDemandRecursion
open CountingMatroid.Analysis.SlotDemandPairing
open CountingMatroid.Analysis.LeafCliqueFlow

theorem CountingMatroid.Analysis.SlotTransportFlow.slot_transport_flow {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (hq : 0 < q) (B : PairedSet n)
    (slots : List (Fin n)) (hnodup : slots.Nodup) (node : DemandNode n)
    (hne : node.holes.Nonempty) (hBR : Disjoint B node.holes)
    (hfree : ∀ t ∈ slots, ∀ c : Bool, (t, c) ∉ B ∧ (t, c) ∉ node.holes)
    (hsize : B.card + node.holes.card + slots.toFinset.card = n + 1)
    (hbalance : CountingMatroid.Analysis.SlotDemandRecursion.Balanced r o₁ o₂ q B slots.toFinset node)
    (W : PairedGround n → ℝ)
    (hWslots : ∀ t ∈ slots, W (t, false) = W (t, true) ∧ 0 < W (t, false))
    (hsplit : SlotSplitControl n r o₁ o₂ q)
    (κ : PairedSet n → PairedSet n → ℝ) (C : ℝ) (hC : 0 < C)
    (hsym : ∀ s t, κ s t = κ t s)
    (hWleaf : ∀ leaf ∈ leafNodes r o₁ o₂ q B slots node,
      ∀ i ∈ leaf.holes, 0 < W i)
    (hcap : ∀ leaf ∈ leafNodes r o₁ o₂ q B slots node,
      ∀ x y : leaf.holes, x ≠ y →
        min (W x * slotTotal r o₁ o₂ q B leaf.holes ∅ x)
          (W y * slotTotal r o₁ o₂ q B leaf.holes ∅ y) ≤
            C * κ (leafVertex B leaf.holes x) (leafVertex B leaf.holes y)) :
    ∃ flow : FlowCertificate κ (completionDemand r o₁ o₂ q B slots.toFinset node),
      flowEnergy κ flow.current ≤ C *
        (nodePotential r o₁ o₂ q B slots.toFinset W node -
          ∑ t ∈ slots.toFinset,
            nodeFuture r o₁ o₂ q B slots.toFinset node t / W (t, false)) := by sorry
