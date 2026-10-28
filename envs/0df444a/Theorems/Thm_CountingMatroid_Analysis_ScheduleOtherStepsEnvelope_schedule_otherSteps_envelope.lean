-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_ScheduleOtherStepsEnvelope_schedule_otherSteps_envelope
-- name    : CountingMatroid.Analysis.ScheduleOtherStepsEnvelope.schedule_otherSteps_envelope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T13:14:18.092782+00:00
-- url     : https://prove2.me/theorems/db00845a-1b89-4d71-86cc-a2618aa9b3b8
-- title:
--   A uniform polynomial envelope for schedule-construction charges
-- statement:
--   For a natural number $m$, set $b(m)=\lfloor\log_2m\rfloor+1$, with $\log_2 0=0$. For a reduced rational $q=u/v$ with $v>0$, set $\ell(q)=2+b(|u|)+b(v)$. Let $p=(\varepsilon,\delta)$ be rational input parameters with $0<\varepsilon<1$ and $0<\delta<1$. Write $W(F)$ for `otherSteps`, the sum of the model’s fair-bit and nonoracle word-operation charges for a charged computation $F$.
--
--   For $n,r\in\mathbb N$, define the encoded input length and the combined size parameter by
--   $$B_{\mathrm{in}}=b(n)+b(r)+\ell(\varepsilon)+\ell(\delta),$$
--   $$S=n+B_{\mathrm{in}}+\lceil\varepsilon^{-1}\rceil_{\mathbb N}+b\!\left(\lceil\delta^{-1}\rceil_{\mathbb N}\right)+1,$$
--   where the natural ceiling truncates below at zero. There exist natural constants $C,d$, independent of $n,r,p$, such that
--   $$W(\operatorname{schedule}(n,p))\le CS^d\qquad\text{for every }n,r,p.$$
--   Here `schedule` is the concrete charged construction of the cooling factor, phase count, tolerance, restart and observation caps, draw budget, and repetition count. The theorem provides a uniform polynomial bound in $n$, the encoded inputs, inverse accuracy, and the binary length of inverse confidence.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ScheduleOtherStepsEnvelope.lean#L48-L235

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
set_option autoImplicit false

namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines

open CountingMatroid.Analysis.ResourceBound (otherSteps_bind)

theorem CountingMatroid.Analysis.ScheduleOtherStepsEnvelope.schedule_otherSteps_envelope :
    ∃ (C degree : ℕ), ∀ (n r : ℕ) (p : InputParams),
      let inputSize := n + binaryInputLength n r p + Nat.ceil p.ε⁻¹ +
        binaryNatLength (Nat.ceil p.δ⁻¹) + 1
      otherSteps (CountingMatroid.Program.schedule n p) ≤
        C * inputSize ^ degree := by sorry
