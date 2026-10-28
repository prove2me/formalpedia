-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_ResourceBound_estimate_none_raw_cost_bound
-- name    : CountingMatroid.Analysis.ResourceBound.estimate_none_raw_cost_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:45:23.28237+00:00
-- url     : https://prove2.me/theorems/c18fe77f-ad9b-491f-a33d-9c316cecec4e
-- title:
--   Explicit resource bound for repeated runs and their median
-- statement:
--   Write $\operatorname{oc}(P)$ for the sum of the two original-oracle charge counters of a computation $P$, and $\operatorname{work}(P)$ for its fair-bit and named nonoracle primitive charges. Fix a feasibility contract: an oracle-based Boolean solver $F$, natural constants $A,d_A,B,d_B$, correctness for full-ground equal-rank matroids represented by exact independence oracles, and uniform bounds $\operatorname{oc}(F)\le A(n+r+1)^{d_A}$ and $\operatorname{work}(F)\le B(n+r+1)^{d_B}$ for every input and every pair of Boolean oracles. Correctness means that $F$ answers true exactly when the represented matroids have a common basis. Let $n,r\in\mathbb N$ and let $o_1,o_2$ be arbitrary Boolean functions on subset queries of $E_n=\{0,\ldots,n-1\}$. Let $p=(\varepsilon,\delta)\in\mathbb Q^2$ satisfy $0<\varepsilon,\delta<1$, and let $\mathcal T:\mathbb N\times\mathbb N\to\{0,1\}$ supply a bit tape for each repeated run. The preprocessing routine returns $1$ when $n=0$; otherwise it invokes $F$, returning $0$ if $F$ answers false and returning no preliminary answer if $F$ answers true. The estimator returns a preliminary answer when present; otherwise it computes the prescribed schedule, runs the capped annealing routine on the supplied tapes, and returns the median of its rational outputs. For $m\in\mathbb N$, define $\lambda(m)=\lfloor\log_2m\rfloor+1$ when $m>0$ and $\lambda(0)=1$. For reduced $a/b\in\mathbb Q$ with $b>0$, put $\ell(a/b)=2+\lambda(|a|)+\lambda(b)$. Let $P$ be preprocessing, let $S_c$ be the charged schedule computation with resulting schedule $s$, and let $N=s.\mathrm{repetitions}$. Suppose $P$ returns no preliminary answer. For a natural $K$, assume that for every tape index $j$, the capped run $U_j$ starting at cursor zero under $s$ satisfies $$\ell(\operatorname{value}(U_j)_1)\le K,\qquad\operatorname{oc}(U_j)\le K,\qquad\operatorname{work}(U_j)\le K.$$ If $E$ is the full estimator computation, then $$\operatorname{oc}(E)\le\operatorname{oc}(P)+\operatorname{oc}(S_c)+NK,$$ $$\operatorname{work}(E)\le\operatorname{work}(P)+\operatorname{work}(S_c)+N(K+1)+(N+1)^2(2K+8).$$
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ResourceBound.lean#L238-L342

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

namespace CountingMatroid.Analysis.ResourceBound
end CountingMatroid.Analysis.ResourceBound
namespace CountingMatroid.Analysis
end CountingMatroid.Analysis
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.ScheduleResourceEnvelope
end CountingMatroid.Analysis.ScheduleResourceEnvelope
namespace CountingMatroid.Analysis.ScheduleCostEnvelope
end CountingMatroid.Analysis.ScheduleCostEnvelope
namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
namespace CountingMatroid.Analysis.LeastHalvingsCost
end CountingMatroid.Analysis.LeastHalvingsCost
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
namespace CountingMatroid.Analysis.OutputSupport
end CountingMatroid.Analysis.OutputSupport
set_option autoImplicit false

namespace CountingMatroid.Analysis.ResourceBound
end CountingMatroid.Analysis.ResourceBound
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ResourceBound

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines
open CountingMatroid.Model.Operations

theorem CountingMatroid.Analysis.ResourceBound.estimate_none_raw_cost_bound (contract : FeasibilityContract)
    (n r : ℕ) (o₁ o₂ : IndependenceOracle n) (p : InputParams)
    (tape : ℕ → ℕ → Bool) (K : ℕ)
    (h : (CountingMatroid.Program.preprocess contract.implementation
      n r o₁ o₂).val = none)
    (hrun : ∀ j,
      let run := CountingMatroid.Program.boundedRun r o₁ o₂ (tape j)
        (CountingMatroid.Program.schedule n p).val 0
      binaryRatLength run.val.1 ≤ K ∧
      oracleCalls run ≤ K ∧ otherSteps run ≤ K) :
    let pre := CountingMatroid.Program.preprocess contract.implementation
      n r o₁ o₂
    let schedule := CountingMatroid.Program.schedule n p
    let T := schedule.val.repetitions
    let run := CountingMatroid.Program.estimate contract.implementation
      n r o₁ o₂ p tape
    oracleCalls run ≤ oracleCalls pre + oracleCalls schedule + T * K ∧
    otherSteps run ≤ otherSteps pre + otherSteps schedule + T * (K + 1) +
      (T + 1) ^ 2 * (2 * K + 8) := by sorry
