-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_ScheduleOtherStepsEnvelope_scheduleOpening_otherSteps_le
-- name    : CountingMatroid.Analysis.ScheduleOtherStepsEnvelope.scheduleOpening_otherSteps_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T13:12:54.950249+00:00
-- url     : https://prove2.me/theorems/aa40491e-74fb-44ab-b13e-39cb64f6be90
-- title:
--   Work bound for the opening stage of schedule construction
-- statement:
--   For a natural number $m$, set $b(m)=\lfloor\log_2m\rfloor+1$, with $\log_2 0=0$. For a reduced rational $q=u/v$ with $v>0$, set $\ell(q)=2+b(|u|)+b(v)$. Let $p=(\varepsilon,\delta)$ be rational input parameters with $0<\varepsilon<1$ and $0<\delta<1$. Write $W(F)$ for `otherSteps`, the sum of the model’s fair-bit and nonoracle word-operation charges for a charged computation $F$.
--
--   For $n\in\mathbb N$, the charged opening stage computes $\varepsilon/10$, runs the bounded halving search on that threshold, forms $2n$, converts it to a rational, computes $1/(2n)$, and subtracts this value from one to obtain the cooling factor. Write $H(q)=\operatorname{leastHalvings}(q)$ for the charged bounded search. Then
--   $$\begin{aligned}W(\operatorname{scheduleOpening}(n,p))\le{}&(\ell(\varepsilon)+7)^2+W(H(\varepsilon/10))\\&+1+(\log_2(2n)+1)\\&+(4+\ell(2n))^2+(4+\ell(1/(2n)))^2.\end{aligned}$$
--   The arguments of $\ell$ are rational values, with natural quantities cast to rationals. The theorem includes $n=0$, using total rational division, for which $1/0=0$. It exposes the halving-search cost and bounds each of the surrounding arithmetic operations.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ScheduleOpeningCost.lean#L110-L143

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

theorem CountingMatroid.Analysis.ScheduleOtherStepsEnvelope.scheduleOpening_otherSteps_le (n : ℕ) (p : InputParams) :
    otherSteps (scheduleOpening n p) ≤
      (binaryRatLength p.ε + 7) ^ 2 +
      otherSteps (CountingMatroid.Program.leastHalvings (p.ε / 10)) +
      1 + ((2 * n).log2 + 1) +
      (4 + binaryRatLength (2 * n : ℚ)) ^ 2 +
      (4 + binaryRatLength (1 / (2 * n : ℚ))) ^ 2 := by sorry
