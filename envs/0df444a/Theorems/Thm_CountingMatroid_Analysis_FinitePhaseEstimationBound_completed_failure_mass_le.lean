-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_FinitePhaseEstimationBound_completed_failure_mass_le
-- name    : CountingMatroid.Analysis.FinitePhaseEstimationBound.completed_failure_mass_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T14:26:53.161496+00:00
-- url     : https://prove2.me/theorems/49d8dc1c-170d-41cf-a7c7-58735dae5ef1
-- title:
--   Second-moment bounds control completed raw-mean failures
-- statement:
--   Let $n,r\in\mathbb N$, $I=\{0,\ldots,n-1\}$, $E=I\times\{0,1\}$, and $\Omega=\mathcal P(E)$. Let $o_1,o_2$ be Boolean oracles on subsets of $I$. Write $R(S)$ for the natural-number value of the paired-rank routine with parameter $r$ and these oracles, and $d(S)=n-R(S)$ with subtraction truncated at zero. Let $p=(\varepsilon,\delta)$ consist of rational parameters $0<\varepsilon,\delta<1$. Write $s=\operatorname{setup}(n,p)$ for the prescribed annealing schedule, $L=s.L$ for its phase count, $\rho=s.\rho$ for its temperature ratio, $\eta=s.\eta$ for its relative mean tolerance, and $N=s.\mathrm{observations}$ for its sample count. A transversal selects one label from each pair; let $T$ be this class. For distinct $i,k\in I$, let $D_{ik}$ be the class having pair $i$ empty, pair $k$ full, and every other pair singly occupied. All other states are invalid. For $q>0$ and positive rational multipliers $w_{ik}$, define $C(q)=\sum_{S\in T}q^{d(S)}$, $D_{ik}(q)=\sum_{S\in D_{ik}}q^{d(S)}$, and $\lambda(S)=q^{d(S)}$ on $T$, $\lambda(S)=w_{ik}q^{d(S)}$ on $D_{ik}$, and $\lambda(S)=0$ on invalid states. Let $Z_w=\sum_S\lambda(S)$ and $\pi(S)=\lambda(S)/Z_w$. The observable indices form $\mathcal O=\{0,1\}\sqcup(I\times I)$. Their functions are $G_0=\mathbf1_T$, $G_1=\mathbf1_T\rho^{d(S)}$, and $G_{ik}=\mathbf1_{D_{ik}}$ for $i\ne k$, with $G_{ii}=\mathbf1_T$. At phase $j$, their true means are taken under the normalized operational law at $q=\rho^j$ and the current multipliers. Empirical means are the corresponding observation-counter averages. A phase cursor $u$ contains a current multiplier table, stored tables, a running product, and a bit cursor. Call it good at phase $j$ if every stored table at level $a\le j$ lies between one quarter and four times $C(\rho^a)/D_{ik}(\rho^a)$, and its current table has the same bounds at level $j$, for all distinct $i,k$. Say phase $j$ has accurate raw means if its actual phase history reaches a good cursor, its restart and observation procedures succeed, $N>0$, and every empirical observable mean lies between $(1-\eta)$ and $(1+\eta)$ times its true mean. Call an observation completed when those operational procedures succeed from a good reached cursor and $N>0$, without requiring mean accuracy. Define $e_\ell(\beta)$ to be the squared empirical-minus-true error for observable $\ell$ on completed observations and zero otherwise. Assume $n>0$, fix any phase index $j\in\mathbb N$ and Boolean prefix $h$, and put $t=\operatorname{blockLength}(n,r,p)-|h|$ with truncated subtraction. Suppose every $\ell\in\mathcal O$ satisfies $$2^{-t}\sum_{v\in\{0,1\}^t}e_\ell(hv)\le\frac{40000n^8}{N}.$$ Then $$2^{-t}|\{v\in\{0,1\}^t:\text{observation is completed on }hv,\ \text{raw means are not accurate}\}|\le\frac1{32(L+1)}.$$
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/FinitePhaseEstimationBound.lean#L67-L132

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
import Definitions.Def_CountingMatroid_Analysis_PhaseObservationExperiment
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
import Definitions.Def_CountingMatroid_Analysis_StationaryMeanIdentities
import Definitions.Def_CountingMatroid_Analysis_StationaryMeanLowerBound
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
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Infix
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

namespace CountingMatroid.Analysis.FinitePhaseEstimationBound
end CountingMatroid.Analysis.FinitePhaseEstimationBound
namespace CountingMatroid.Analysis.FiniteObservationMarkov
end CountingMatroid.Analysis.FiniteObservationMarkov
namespace CountingMatroid.Analysis.FiniteTapePrefixBound
end CountingMatroid.Analysis.FiniteTapePrefixBound
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

namespace CountingMatroid.Analysis.FinitePhaseEstimationBound
end CountingMatroid.Analysis.FinitePhaseEstimationBound
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.FinitePhaseEstimationBound

open CountingMatroid.Model CountingMatroid.Program CountingMatroid.Model.Operations
open CountingMatroid.Analysis.PhaseObservationExperiment
open CountingMatroid.Analysis.FiniteObservationMarkov
open CountingMatroid.Analysis.RelativeObservationBounds

theorem CountingMatroid.Analysis.FinitePhaseEstimationBound.completed_failure_mass_le (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (j : ℕ) (pref : List Bool)
    (hmoment : ∀ index : Observable n,
      let s := CountingMatroid.Interface.Pseudocode.setup n p
      let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
      (∑ suffix : List.Vector Bool t,
        observationSquaredError r o₁ o₂
          (fun i => ((pref ++ suffix.val)[i]?).getD false) s j index) /
          (2 : ℚ) ^ t ≤ 40000 * (n : ℚ) ^ 8 / s.observations) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
    (Set.ncard {suffix : List Bool | suffix.length = t ∧
      ObservationCompleted r o₁ o₂
        (fun i => ((pref ++ suffix)[i]?).getD false) s j ∧
      ¬ PhaseMeanCertificate.RawPhaseMeans r o₁ o₂
        (fun i => ((pref ++ suffix)[i]?).getD false) s j} : ENNReal) *
      (1 / 2 : ENNReal) ^ t ≤ 1 / (32 * ((s.L : ENNReal) + 1)) := by sorry
