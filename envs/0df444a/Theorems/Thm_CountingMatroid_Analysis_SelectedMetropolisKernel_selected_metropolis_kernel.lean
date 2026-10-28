-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_SelectedMetropolisKernel_selected_metropolis_kernel
-- name    : CountingMatroid.Analysis.SelectedMetropolisKernel.selected_metropolis_kernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:38:29.746984+00:00
-- url     : https://prove2.me/theorems/cb3815e3-b2e3-4aa8-90df-467d88839125
-- title:
--   The ideal exchange kernel in occupied and unoccupied index coordinates
-- statement:
--   Let $n,r\in\mathbb N$ with $n>0$, let $o_1,o_2$ be arbitrary Boolean independence-query functions on subsets of $[n]$, and let $q\in\mathbb Q$ satisfy $q>0$. Let $w_{ik}>0$ be rational multipliers for every distinct ordered pair $i,k\in[n]$. Paired states are subsets of $[n]\times\{0,1\}$. Their operational weights are $q^{d(S)}$ on transversals, $w_{ik}q^{d(S)}$ on states with empty pair $i$ and full pair $k$, and zero on invalid states, where $d(S)=n-\operatorname{pairedRank}(r,o_1,o_2,S)$ uses truncated natural subtraction and the program’s oracle scans. Let $\pi$ be their normalized real probability distribution.
--
--   Fix states $S,T$ with $|S|=n$, with no cardinality condition on $T$. The program’s deterministic selectors enumerate the occupied labels $a_i\in S$ and unoccupied labels $b_j\notin S$, for $i,j\in[n]$. Set $S_{ij}=(S\setminus\{a_i\})\cup\{b_j\}$ and
--   $$E(S,Z,T;a)=a\mathbf1_{\{Z=T\}}+(1-a)\mathbf1_{\{S=T\}}.$$
--   The ideal Metropolis chain, whose proposal swaps two independent uniformly chosen paired labels, has the kernel
--   $$P(S,T)=\frac12\mathbf1_{\{S=T\}}+\frac1{2n^2}\sum_{i\in[n]}\sum_{j\in[n]}E\!\left(S,S_{ij},T;\min\left(1,\frac{\pi(S_{ij})}{\pi(S)}\right)\right).$$
--   This identifies the ideal kernel with a half-holding step followed by the indexed exchange-and-acceptance average.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/SelectedMetropolisKernel.lean#L61-L96

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
import Definitions.Def_CountingMatroidSupport_Probability_Bilinear
import Definitions.Def_CountingMatroidSupport_Probability_FinDist
import Definitions.Def_CountingMatroidSupport_Probability_FinDistFunctional
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhase
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseHistory
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseWork
import Definitions.Def_CountingMatroid_Analysis_DefectPartitionPositive
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseWork
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_IdealExchangeChain
import Definitions.Def_CountingMatroid_Analysis_InitialMultipliersGood
import Definitions.Def_CountingMatroid_Analysis_ObservePhaseWork
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
import Definitions.Def_CountingMatroid_Analysis_SelectedMetropolisKernel
import Definitions.Def_CountingMatroid_Analysis_SelectedPairedBijection
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
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF

namespace CountingMatroid.Analysis.ExchangeProposalGeometry
end CountingMatroid.Analysis.ExchangeProposalGeometry
namespace Arlib
end Arlib
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
namespace CountingMatroid.Analysis.ClassifiedStateSelection
end CountingMatroid.Analysis.ClassifiedStateSelection
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! The ideal Metropolis kernel in the program's selection-index coordinates.
Rejected proposals contribute to the diagonal, including proposals of weight zero. -/
namespace CountingMatroid.Analysis.SelectedMetropolisKernel
end CountingMatroid.Analysis.SelectedMetropolisKernel
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.SelectedMetropolisKernel
open CountingMatroid.Model
open CountingMatroid.Analysis.IdealExchangeChain
open CountingMatroid.Analysis.SelectedPairedBijection
open Arlib.MarkovChains

theorem CountingMatroid.Analysis.SelectedMetropolisKernel.selected_metropolis_kernel {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (weights : Multipliers n)
    (hn : 0 < n) (hq : 0 < q) (hw : ∀ a, 0 < weights a)
    (state next : PairedSet n) (hcard : state.card = n) :
    idealChain r o₁ o₂ q weights hn hq hw state next =
      (1 / 2 : ℝ) * (if state = next then 1 else 0) +
      (1 / (2 * (n : ℝ) ^ 2)) * ∑ i : Fin n, ∑ j : Fin n,
        exchangeOutcome state
          (insert (selectedLabel state false hcard j).val
            (state.erase (selectedLabel state true hcard i).val)) next
          (min 1 ((operationalLaw r o₁ o₂ q weights hq hw)
            (insert (selectedLabel state false hcard j).val
              (state.erase (selectedLabel state true hcard i).val)) /
            (operationalLaw r o₁ o₂ q weights hq hw) state)) := by sorry
