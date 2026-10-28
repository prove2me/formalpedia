-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_ScheduleOtherStepsEnvelope_thermalRest_otherSteps_poly
-- name    : CountingMatroid.Analysis.ScheduleOtherStepsEnvelope.thermalRest_otherSteps_poly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T13:08:00.310072+00:00
-- url     : https://prove2.me/theorems/67e55202-80be-4b47-acdb-5822531faa5b
-- title:
--   Polynomial nonoracle bound for the schedule tail
-- statement:
--   Let $n,r\in\mathbb N$ and let rational input parameters satisfy $0<\varepsilon,\delta<1$. For $m\in\mathbb N$, put $\ell_N(m)=\lfloor\log_2m\rfloor+1$, with $\log_2 0=0$. For a reduced rational $x$ with positive denominator, put $\ell_Q(x)=2+\ell_N(|\operatorname{num}(x)|)+\ell_N(\operatorname{den}(x))$. Define the input encoding length and size parameter by $$B=\ell_N(n)+\ell_N(r)+\ell_Q(\varepsilon)+\ell_Q(\delta),\qquad S=n+B+\lceil\varepsilon^{-1}\rceil_++\ell_N(\lceil\delta^{-1}\rceil_+)+1,$$ where $\lceil x\rceil_+=\max(0,\lceil x\rceil)$. Let $b$ be the returned counter of the bounded halving search at threshold $\varepsilon/10$, and put $$L=2n(n+b),\qquad D=32(L+1),\qquad\eta=\varepsilon/D,\qquad\rho=1-\frac1{2n}.$$ Let $t$ be the thermal record with opening fields $(b,\rho,2n)$ and fields $(L,L+1,D,\eta)$. Write $W(A)$ for the source's nonoracle charge of a computation $A$, namely fair-bit reads plus its named nonoracle instruction tallies. The schedule tail, which computes the trace length, restart and observation caps, draw-trial cap, and confidence repetitions, satisfies $$W(\operatorname{thermalRest}(n,p,t))\le10^{150}S^{40}.$$
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ScheduleThermalRestCost.lean#L65-L256

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

theorem CountingMatroid.Analysis.ScheduleOtherStepsEnvelope.thermalRest_otherSteps_poly (n r : ℕ) (p : InputParams) :
    let S := n + binaryInputLength n r p + Nat.ceil p.ε⁻¹ +
      binaryNatLength (Nat.ceil p.δ⁻¹) + 1
    let b := (CountingMatroid.Program.leastHalvings (p.ε / 10)).val
    let L := 2 * n * (n + b)
    let D := 32 * (L + 1)
    otherSteps (thermalRest n p
      ⟨⟨b, 1 - 1 / (2 * n : ℚ), 2 * n⟩, L, L + 1, D, p.ε / (D : ℚ)⟩) ≤
      10 ^ 150 * S ^ 40 := by sorry
