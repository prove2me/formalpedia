-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_PhaseObservationExperiment_raw_means_iff_observation_data
-- name    : CountingMatroid.Analysis.PhaseObservationExperiment.raw_means_iff_observation_data
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T14:16:39.48999+00:00
-- url     : https://prove2.me/theorems/96156ff9-f4cb-43a5-a594-41a3d463f942
-- title:
--   Raw phase means as accuracy of a finite observable family
-- statement:
--   Let $n,r\in\mathbb N$, and let $o_1,o_2$ be arbitrary Boolean independence-query functions on subsets of $[n]=\{0,\ldots,n-1\}$. Let $t:\mathbb N\to\{0,1\}$ be any tape, $s$ any schedule, $j\in\mathbb N$, and write $\rho=s.\rho$, $\eta=s.\eta$, $N=s.\mathrm{observations}$.
--
--   For paired states $S\subseteq[n]\times\{0,1\}$, let $d(S)=n-\operatorname{pairedRank}(r,o_1,o_2,S)$ with truncated subtraction. A transversal has one label per pair; a defect $(i,k)$ has the empty pair $i$ and full pair $k$, with $i\ne k$. Write $C_a$ for the sum of $(\rho^a)^{d(S)}$ over transversals and $D_{a,ik}$ for that sum over defect $(i,k)$. Put $I_{a,ik}=C_a/D_{a,ik}$. A cursor $c$ has good stored multipliers at phase $j$ when every table entry at $a\le j$ lies between $I_{a,ik}/4$ and $4I_{a,ik}$, and its current weight $w_{ik}$ lies between $I_{j,ik}/4$ and $4I_{j,ik}$.
--
--   At phase $j$, give a transversal weight $(\rho^j)^{d(S)}$, a defect weight $w_{ik}(\rho^j)^{d(S)}$, and an invalid state weight zero. Divide finite weighted sums by their total $Z$ to define the type means $m_0,m_{ik}$ and the mean $m_U$ of the observable $\rho^{d(S)}$ on transversals and zero elsewhere. For an observation output with counts $c_0,c_{ik}$, numerator sum $u$, and sample size $N$, put $\widehat m_0=c_0/N$, $\widehat m_{ik}=c_{ik}/N$, and $\widehat m_U=u/N$. Define relative accuracy by
--   $$\operatorname{Rel}_{\eta}(m,\widehat m)\iff(1-\eta)m\le\widehat m\le(1+\eta)m.$$
--
--   Let $\mathcal O=\{\mathrm{false},\mathrm{true}\}\sqcup([n]\times[n])$. The false index selects the transversal indicator, true selects the numerator observable, an off-diagonal pair selects its defect indicator, and a diagonal pair repeats the transversal indicator. Denote the corresponding means and empirical means by $m_\alpha(c)$ and $\widehat m_\alpha(o)$. The optional data operation $\operatorname{Data}_j(t)$ runs the actual phase history, restart, and observation procedure, returning the reached cursor $c$ and observation output $o$ exactly when all three succeed. Then
--   $$\operatorname{RawPhaseMeans}_j(t)\iff\exists c,o:\ \operatorname{Data}_j(t)=\operatorname{some}(c,o),\quad\operatorname{GoodStored}_j(c),\quad N>0,\quad\forall\alpha\in\mathcal O,\ \operatorname{Rel}_{\eta}(m_\alpha(c),\widehat m_\alpha(o)).$$
--   Here `RawPhaseMeans` is the same successful-history, good-weight, and positive-sample condition with separate relative estimates for the transversal, numerator, and every distinct-index defect. This equivalence packages those conditions into one finite observable family.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/PhaseObservationExperiment.lean#L94-L125

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

namespace CountingMatroid.Analysis.PhaseObservationExperiment
end CountingMatroid.Analysis.PhaseObservationExperiment
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.PhaseObservationExperiment

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.StationaryMeanIdentities
open CountingMatroid.Analysis.RelativeObservationBounds

theorem CountingMatroid.Analysis.PhaseObservationExperiment.raw_means_iff_observation_data {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool) (s : AnnealingSchedule) (j : ℕ) :
    PhaseMeanCertificate.RawPhaseMeans r o₁ o₂ tape s j ↔
      ∃ current observed,
        phaseObservationData r o₁ o₂ tape s j = some (current, observed) ∧
        FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂ s j current ∧
        0 < s.observations ∧ ∀ index : Observable n,
          RelativeEstimate s.η (observableMean r o₁ o₂ s j current index)
            (empiricalMean s observed index) := by sorry
