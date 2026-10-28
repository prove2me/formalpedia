-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_ScheduleOtherStepsEnvelope_thermalRest_cost_eq
-- name    : CountingMatroid.Analysis.ScheduleOtherStepsEnvelope.thermalRest_cost_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T13:03:07.238679+00:00
-- url     : https://prove2.me/theorems/17847799-f400-48e0-bc22-01da0a97be15
-- title:
--   Exact cost decomposition of the schedule tail
-- statement:
--   Let $n\in\mathbb N$ and let input parameters $p=(\varepsilon,\delta)$ be rational with $0<\varepsilon,\delta<1$. A thermal record $t$ stores an opening triple $(b,\rho,m)$ with $b,m\in\mathbb N$ and $\rho\in\mathbb Q$, natural fields $L,U,D$, and a rational field $\eta$. Here $U$ is the field named LPlusOne; for an arbitrary record no equation $U=L+1$ is assumed. The schedule-tail procedure computes the trace length, restart cap, observation count, draw cap, and confidence repetitions from this record and the input parameters. Put $$A=10^{10}Un^{14},\qquad R=2000U^2n^2\bigl(20n^4(nU+2)\bigr),\qquad Q=\frac{A}{\eta^2},\qquad N_Q=\max(0,\lceil Q\rceil).$$ Rational division is total. Write $W(A)$ for the source's nonoracle charge of a computation $A$, namely fair-bit reads plus its named nonoracle instruction tallies. Let $\operatorname{mul}_{\mathbb Q}$, $\operatorname{div}_{\mathbb Q}$, and $\operatorname{ceil}_+$ denote the charged rational multiplication, division, and natural-valued ceiling primitives. Then $$\begin{aligned}W(\operatorname{thermalRest}(n,p,t))={}&W(\operatorname{natPower}(n,4))+W(\operatorname{natPower}(U,2))\\&+W(\operatorname{natPower}(n,2))+W(\operatorname{natPower}(n,14))\\&+14+\lfloor\log_2 A\rfloor+1\\&+W(\operatorname{mul}_{\mathbb Q}(\eta,\eta))+W(\operatorname{div}_{\mathbb Q}(A,\eta^2))\\&+W(\operatorname{ceil}_+(Q))+W(\operatorname{leastDrawTrials}(3L(R+N_Q)))\\&+W(\operatorname{leastHalvings}(\delta)).\end{aligned}$$ The natural logarithm convention is $\log_2 0=0$.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ScheduleThermalRestCost.lean#L21-L63

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
/-!
# Cost of the schedule tail

The setup phases have separate checked cost bounds. This module proves an exact
cost identity for the charged powers, observation count, draw width, and confidence
repetition computation, and bounds their sum by the prescribed polynomial.
Intermediate encoding lengths are bounded using the shared length and capped-search
lemmas in `ScheduleCostPrimitives`.
-/

set_option autoImplicit false

namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines

theorem CountingMatroid.Analysis.ScheduleOtherStepsEnvelope.thermalRest_cost_eq (n : ℕ) (p : InputParams) (t : ThermalResult) :
    let A := 10000000000 * t.LPlusOne * (CountingMatroid.Program.natPower n 14).val
    let R := 2000 * (CountingMatroid.Program.natPower t.LPlusOne 2).val *
      (CountingMatroid.Program.natPower n 2).val *
      (20 * (CountingMatroid.Program.natPower n 4).val * (n * t.LPlusOne + 2))
    let Q := (A : ℚ) / (t.eta * t.eta)
    otherSteps (thermalRest n p t) =
      otherSteps (CountingMatroid.Program.natPower n 4) +
      otherSteps (CountingMatroid.Program.natPower t.LPlusOne 2) +
      otherSteps (CountingMatroid.Program.natPower n 2) +
      otherSteps (CountingMatroid.Program.natPower n 14) + 14 + (A.log2 + 1) +
      otherSteps (CountingMatroid.Model.Operations.ratMul t.eta t.eta) +
      otherSteps (CountingMatroid.Model.Operations.ratDiv (A : ℚ) (t.eta * t.eta)) +
      otherSteps (CountingMatroid.Model.Operations.rationalCeil Q) +
      otherSteps (CountingMatroid.Program.leastDrawTrials
        (3 * t.L * (R + (CountingMatroid.Model.Operations.rationalCeil Q).val))) +
      otherSteps (CountingMatroid.Program.leastHalvings p.δ) := by sorry
