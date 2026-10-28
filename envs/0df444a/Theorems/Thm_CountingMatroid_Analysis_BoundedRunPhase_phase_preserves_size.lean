-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_BoundedRunPhase_phase_preserves_size
-- name    : CountingMatroid.Analysis.BoundedRunPhase.phase_preserves_size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T13:08:06.42309+00:00
-- url     : https://prove2.me/theorems/5e3bc3fc-d7e8-46a7-8379-c7db92ad0840
-- title:
--   One bounded phase preserves the rational-size invariant
-- statement:
--   Let $n,r\in\mathbb N$, let $o_1,o_2$ be Boolean oracles on subset indicators of an $n$-element set, and fix a tape $t:\mathbb N\to\{0,1\}$. For an annealing schedule $s$, write $L=s.L$, $\tau=s.\tau$, $B=s.\mathrm{restartCap}$, $M=s.\mathrm{observations}$, and $T=s.\mathrm{drawTrials}$ for its phase count, trace-transition count, restart-attempt cap, observation count, and draw-trial cap. Let $\rho=s.\rho$ and define $$S=n+L+\tau+B+M+T+\ell(\rho)+1,$$ where $\ell(a/b)=2+(\lfloor\log_2|a|\rfloor+1)+(\lfloor\log_2 b\rfloor+1)$ for a reduced rational with positive denominator, with $\log_2 0=0$ in this length convention. Assume $\rho\ge0$. For an optional annealing cursor $a$, let $I(S,j,a)$ mean that, whenever $a$ is present, each current multiplier, each stored multiplier at every phase index, and its accumulated product has rational length at most $(j+1)S^{10}$. A cursor contains these weights, the product, and a tape position; an absent cursor denotes an aborted run and satisfies $I$ vacuously. Let $j<L$ and assume $I(S,j,a)$. If $a^\prime$ is the value returned by the phase-$j$ body from $a$, then $$I(S,j+1,a^\prime).$$ Thus each phase advances the common rational-length budget from $(j+1)S^{10}$ to $(j+2)S^{10}$. This invariant controls subsequent arithmetic charges.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/BoundedRunPhaseSize.lean#L19-L140

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Dict
import Definitions.Def_CountingMatroidSupport_Computation_Heap
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Num
import Definitions.Def_CountingMatroidSupport_Computation_Queue
import Definitions.Def_CountingMatroidSupport_Computation_Rand
import Definitions.Def_CountingMatroidSupport_Computation_Roster
import Definitions.Def_CountingMatroidSupport_Computation_Slot
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroidSupport_Computation_Std
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhase
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
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

namespace CountingMatroid.Analysis.BoundedRunPhase
end CountingMatroid.Analysis.BoundedRunPhase
namespace CountingMatroid.Analysis.FinishPhaseWeightsSize
end CountingMatroid.Analysis.FinishPhaseWeightsSize
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
namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope
end CountingMatroid.Analysis.BoundedRunResourceEnvelope
/-!
One bounded phase preserves the rational-size invariant for current weights,
stored tables, and the accumulated product. Abort branches satisfy the invariant
vacuously. Successful phases use the observation count and accumulator-height
bounds from `PhaseResourcePrimitives` and the multiplier scan bound from
`FinishPhaseWeightsSize`; the resulting ratio fits one phase increment.
-/

set_option autoImplicit false
namespace CountingMatroid.Analysis.BoundedRunPhase
end CountingMatroid.Analysis.BoundedRunPhase
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.BoundedRunPhase
open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines CountingMatroid.Program

theorem CountingMatroid.Analysis.BoundedRunPhase.phase_preserves_size {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (hρ : 0 ≤ s.ρ)
    (j : ℕ) (hj : j < s.L) (acc : Option (AnnealingCursor n))
    (hacc : PhaseSizeInvariant (runSize n s) j acc) :
    PhaseSizeInvariant (runSize n s) (j + 1)
      (boundedRunPhase r o₁ o₂ tape s j acc).val := by sorry
