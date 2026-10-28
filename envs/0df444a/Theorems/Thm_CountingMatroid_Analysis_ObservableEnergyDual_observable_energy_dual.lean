-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_ObservableEnergyDual_observable_energy_dual
-- name    : CountingMatroid.Analysis.ObservableEnergyDual.observable_energy_dual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T14:27:14.741158+00:00
-- url     : https://prove2.me/theorems/b12bd979-7495-4f58-b920-549a2ee2fc6c
-- title:
--   An observable Poincaré bound implies a dual energy inequality
-- statement:
--   Let $n,r\in\mathbb N$, $I=\{0,\ldots,n-1\}$, $E=I\times\{0,1\}$, and $\Omega=\mathcal P(E)$. Let $o_1,o_2$ be Boolean oracles on subsets of $I$. Write $R(S)$ for the natural-number value of the paired-rank routine with parameter $r$ and these oracles, and $d(S)=n-R(S)$ with subtraction truncated at zero. A transversal selects one label from each pair; let $T$ be this class. For distinct $i,k\in I$, let $D_{ik}$ be the class having pair $i$ empty, pair $k$ full, and every other pair singly occupied. All other states are invalid. For $q>0$ and positive rational multipliers $w_{ik}$, define $C(q)=\sum_{S\in T}q^{d(S)}$, $D_{ik}(q)=\sum_{S\in D_{ik}}q^{d(S)}$, and $\lambda(S)=q^{d(S)}$ on $T$, $\lambda(S)=w_{ik}q^{d(S)}$ on $D_{ik}$, and $\lambda(S)=0$ on invalid states. Let $Z_w=\sum_S\lambda(S)$ and $\pi(S)=\lambda(S)/Z_w$. For a state function $H:\Omega\to\mathbb R$, let $\Pi H$ agree with $H$ on transversals, equal the $\pi$-conditional mean of $H$ on each defect class, and be zero on invalid states. A conditional mean on a zero-mass class is defined to be zero. Use $\langle f,g\rangle_\pi=\sum_S\pi(S)f(S)g(S)$, $\mathbb E_\pi f=\sum_S\pi(S)f(S)$, and $\operatorname{Var}_\pi f=\mathbb E_\pi[(f-\mathbb E_\pi f)^2]$. Let $P$ be any Markov kernel on $\Omega$, let $G:\Omega\to\mathbb R$, and let $c:I\times I\to\mathbb R$ satisfy $G(S)=c(i,k)$ on every defect class $D_{ik}$. Let $K\in\mathbb R$ and assume $\operatorname{Var}_\pi(\Pi H)\le K\mathcal D_{\pi,P}(H)$ for every $H$, where $\mathcal D_{\pi,P}(H)=\frac12\sum_{S,U}\pi(S)P(S,U)(H(S)-H(U))^2$. Then $$\langle G-\mathbb E_\pi G,H\rangle_\pi^2\le K\,\operatorname{Var}_\pi(G)\,\mathcal D_{\pi,P}(H)\quad\text{for every }H.$$
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ObservableEnergyDual.lean#L112-L152

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

namespace CountingMatroid.Analysis.ObservableEnergyDual
end CountingMatroid.Analysis.ObservableEnergyDual
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
The dual energy inequality used by the stationary time-average estimate.
Orthogonality is expressed through the actual weighted classifier fibers,
including zero-mass fibers and invalid states.
-/
namespace CountingMatroid.Analysis.ObservableEnergyDual
end CountingMatroid.Analysis.ObservableEnergyDual
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ObservableEnergyDual

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.IdealExchangeChain
open CountingMatroid.Analysis.ObservableProjection
open Arlib.Probability Arlib.Probability.FinDist Arlib.MarkovChains

theorem CountingMatroid.Analysis.ObservableEnergyDual.observable_energy_dual {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (w : Multipliers n)
    (hq : 0 < q) (hw : ∀ index, 0 < w index)
    (P : FinChain (PairedSet n)) (G : PairedSet n → ℝ)
    (c : Fin n → Fin n → ℝ)
    (hG : ∀ i k state, (classifyState state).val = .defect i k → G state = c i k)
    (K : ℝ) (henergy : ∀ H,
      Var (operationalLaw r o₁ o₂ q w hq hw)
        (observableProjection (operationalLaw r o₁ o₂ q w hq hw) H) ≤
      K * dirichlet (operationalLaw r o₁ o₂ q w hq hw) P H H) :
    let π := operationalLaw r o₁ o₂ q w hq hw
    ∀ H, (ip π (fun x => G x - Ex π G) H) ^ 2 ≤
      (K * Var π G) * dirichlet π P H H := by sorry
