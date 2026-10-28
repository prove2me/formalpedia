-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_ScheduleOtherStepsEnvelope_thermalSetup_otherSteps_le
-- name    : CountingMatroid.Analysis.ScheduleOtherStepsEnvelope.thermalSetup_otherSteps_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T13:10:10.633649+00:00
-- url     : https://prove2.me/theorems/efb51b49-4c18-4eff-bd37-56566f977389
-- title:
--   Thermal setup work is controlled by denominator length
-- statement:
--   For a natural number $m$, set $b(m)=\lfloor\log_2m\rfloor+1$, with $\log_2 0=0$. For a reduced rational $q=u/v$ with $v>0$, set $\ell(q)=2+b(|u|)+b(v)$. Let $p=(\varepsilon,\delta)$ be rational input parameters with $0<\varepsilon<1$ and $0<\delta<1$. Write $W(F)$ for `otherSteps`, the sum of the model’s fair-bit and nonoracle word-operation charges for a charged computation $F$.
--
--   Let $n\in\mathbb N$ and let $h$ be any schedule-opening record, with natural fields $v=h.\mathrm{twoN}$ and $b_\varepsilon=h.\mathrm{b\varepsilon}$ and rational cooling field $h.\rho$. Put
--   $$D=32\bigl(v(n+b_\varepsilon)+1\bigr).$$
--   The charged thermal setup computes $L=v(n+b_\varepsilon)$, $L+1$, $D$, and the rational tolerance $\eta=\varepsilon/D$, returning them with $h$. Its work satisfies
--   $$W(\operatorname{thermalSetup}(n,p,h))\le5+\log_2D+\bigl(\ell(\varepsilon)+\ell(D)\bigr)^2,$$
--   where $D$ is cast to a rational inside $\ell(D)$. This separates the fixed natural arithmetic and conversion charges from the rational division charge.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ScheduleThermalSetupCost.lean#L112-L128

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
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
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

namespace CountingMatroid.Analysis.LeastHalvingsCost
end CountingMatroid.Analysis.LeastHalvingsCost
namespace CountingMatroid.Analysis
end CountingMatroid.Analysis
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
set_option autoImplicit false
open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines
namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

theorem CountingMatroid.Analysis.ScheduleOtherStepsEnvelope.thermalSetup_otherSteps_le (n : ℕ) (p : InputParams)
    (head : ScheduleOpeningResult) :
    let D := 32 * (head.twoN * (n + head.bε) + 1)
    otherSteps (thermalSetup n p head) ≤
      5 + D.log2 + (binaryRatLength p.ε + binaryRatLength (D : ℚ)) ^ 2 := by sorry
