-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_ScheduleResourceEnvelope_schedule_resource_envelope
-- name    : CountingMatroid.Analysis.ScheduleResourceEnvelope.schedule_resource_envelope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:07:07.313261+00:00
-- url     : https://prove2.me/theorems/e84ae5fa-07b6-47ac-b288-1b0547e5af4f
-- title:
--   A common polynomial bound for schedule values and construction work
-- statement:
--   Let $n,r\in\mathbb N$ and let $p=(\varepsilon,\delta)$ contain rational parameters $0<\varepsilon<1$ and $0<\delta<1$. For $m\in\mathbb N$, let $b(m)=\lfloor\log_2m\rfloor+1$, with $\log_2 0=0$. For a reduced rational $q=u/v$ with $v>0$, let $\ell(q)=2+b(|u|)+b(v)$. Define $B_{\mathrm{in}}=b(n)+b(r)+\ell(\varepsilon)+\ell(\delta)$ and $$S=n+B_{\mathrm{in}}+\lceil\varepsilon^{-1}\rceil_++b(\lceil\delta^{-1}\rceil_+)+1,$$ where $\lceil x\rceil_+=\max(0,\lceil x\rceil)$. For a charged computation $F$, let $Q(F)$ count the first and second original-oracle charges, and let $W(F)$ sum fair-bit and nonoracle word-operation charges.
--
--   Let $F=\operatorname{schedule}(n,p)$ be the concrete charged schedule construction and let $s$ be its returned schedule. Write $\rho,L,\tau,R,N,T,m$ for its cooling factor, phase count, trace length, restart cap, observation count, draw-trial cap, and repetition count. There exist natural constants $C,d$, independent of $n,r,p$, such that
--   $$\rho\ge0,\qquad n+L+\tau+R+N+T+\ell(\rho)+m+1\le CS^d,$$
--   $$Q(F)\le CS^d,\qquad W(F)\le CS^d.$$
--   This combines the numerical loop-cap bounds and the construction’s two resource counters into one uniform schedule envelope.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ScheduleResourceEnvelope.lean#L32-L87

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
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseWork
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseWork
import Definitions.Def_CountingMatroid_Analysis_ObservePhaseWork
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_ScheduleDrawTrialsBridge
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
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

namespace CountingMatroid.Analysis.ScheduleResourceEnvelope
end CountingMatroid.Analysis.ScheduleResourceEnvelope
namespace CountingMatroid.Analysis.ScheduleCostEnvelope
end CountingMatroid.Analysis.ScheduleCostEnvelope
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
namespace CountingMatroid.Analysis.ScheduleValueEnvelope
end CountingMatroid.Analysis.ScheduleValueEnvelope
namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope
end CountingMatroid.Analysis.BoundedRunResourceEnvelope
namespace CountingMatroid.Analysis.BoundedRunOtherSteps
end CountingMatroid.Analysis.BoundedRunOtherSteps
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
set_option autoImplicit false

namespace CountingMatroid.Analysis.ScheduleResourceEnvelope
end CountingMatroid.Analysis.ScheduleResourceEnvelope
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ScheduleResourceEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines

theorem CountingMatroid.Analysis.ScheduleResourceEnvelope.schedule_resource_envelope :
    ∃ (C degree : ℕ), ∀ (n r : ℕ) (p : InputParams),
      let inputSize := n + binaryInputLength n r p + Nat.ceil p.ε⁻¹ +
        binaryNatLength (Nat.ceil p.δ⁻¹) + 1
      let schedule := CountingMatroid.Program.schedule n p
      let s := schedule.val
      0 ≤ s.ρ ∧
      n + s.L + s.τ + s.restartCap + s.observations + s.drawTrials +
        binaryRatLength s.ρ + s.repetitions + 1 ≤ C * inputSize ^ degree ∧
      oracleCalls schedule ≤ C * inputSize ^ degree ∧
      otherSteps schedule ≤ C * inputSize ^ degree := by sorry
