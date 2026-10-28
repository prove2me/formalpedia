-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_EmpiricalPhaseCertificate_observation_estimates_finish
-- name    : CountingMatroid.Analysis.EmpiricalPhaseCertificate.observation_estimates_finish
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T14:14:36.514582+00:00
-- url     : https://prove2.me/theorems/3cadf00c-a93e-46e3-86a2-9e6cc3377692
-- title:
--   Relative observation estimates certify successful phase finishing
-- statement:
--   Let $n\in\mathbb N$, let $s$ be an annealing schedule with observation count $N$, phase count $L$, and tolerance $\eta$, and let $j\in\mathbb N$. Let $w$ be rational multipliers on ordered distinct pair indices $\alpha$, and let an observation cursor have transversal count $c_0$, defect counts $c_\alpha$, and rational numerator sum $U$ (together with a paired state and tape position). Let $R\in\mathbb Q$ be a target ratio, and let $I,I'$ be rational ideal-multiplier tables. Suppose there are rational numbers $p_0>0$ and $p_\alpha>0$ such that $N>0$, $R>0$, $w_\alpha>0$, $$I_\alpha=w_\alpha p_0/p_\alpha,\qquad I_\alpha/2\le I'_\alpha\le2I_\alpha,$$ and the empirical quantities satisfy $$\left|\frac{c_0}{N}-p_0\right|\le\eta p_0,\qquad\left|\frac{U}{N}-p_0R\right|\le\eta p_0R,\qquad\left|\frac{c_\alpha}{N}-p_\alpha\right|\le\eta p_\alpha\quad\text{for every }\alpha.$$ If $0\le\eta\le1/3$, finishing phase $j$ succeeds with a ratio $\widehat R$ and next multipliers $w'$ such that $$\frac{1-\eta}{1+\eta}\le\frac{\widehat R}{R}\le\frac{1+\eta}{1-\eta}.$$ Whenever $j+1<L$, they also satisfy $$I'_\alpha/4\le w'_\alpha\le4I'_\alpha\quad\text{for every }\alpha.$$ This is a deterministic implication of empirical bounds; no independent-sampling or probability normalization assumptions on the $p$ values are required.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/EmpiricalPhaseCertificate.lean#L36-L102

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
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseHistory
import Definitions.Def_CountingMatroid_Analysis_EmpiricalPhaseCertificate
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseEmpiricalUpdate
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
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

namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
namespace CountingMatroid.Analysis.LeastHalvingsCost
end CountingMatroid.Analysis.LeastHalvingsCost
namespace CountingMatroid.Analysis
end CountingMatroid.Analysis
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
set_option autoImplicit false

namespace CountingMatroid.Analysis.EmpiricalPhaseCertificate
end CountingMatroid.Analysis.EmpiricalPhaseCertificate
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.EmpiricalPhaseCertificate

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.RelativeObservationBounds
open CountingMatroid.Analysis.FinishPhaseEmpiricalUpdate

theorem CountingMatroid.Analysis.EmpiricalPhaseCertificate.observation_estimates_finish {n : ℕ} (s : AnnealingSchedule) (j : ℕ)
    (weights : Multipliers n) (observed : ObservationCursor n)
    (R : ℚ) (ideal nextIdeal : Multipliers n)
    (hη : 0 ≤ s.η) (hηsmall : s.η ≤ 1 / 3)
    (hobs : ObservationEstimates s weights observed R ideal nextIdeal) :
    ∃ ratio : ℚ, ∃ nextWeights : Multipliers n,
      (finishPhase s j weights observed).val = some (ratio, nextWeights) ∧
      (1 - s.η) / (1 + s.η) ≤ ratio / R ∧
      ratio / R ≤ (1 + s.η) / (1 - s.η) ∧
      (j + 1 < s.L → ∀ index,
        nextIdeal index / 4 ≤ nextWeights index ∧
        nextWeights index ≤ 4 * nextIdeal index) := by sorry
