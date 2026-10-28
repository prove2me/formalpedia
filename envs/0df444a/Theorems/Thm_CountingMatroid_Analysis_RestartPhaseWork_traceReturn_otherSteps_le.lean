-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_RestartPhaseWork_traceReturn_otherSteps_le
-- name    : CountingMatroid.Analysis.RestartPhaseWork.traceReturn_otherSteps_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:49:19.897321+00:00
-- url     : https://prove2.me/theorems/e007a525-cb28-4dc0-a738-f279c75f11ae
-- title:
--   Nonoracle work bound for a capped trace return
-- statement:
--   Let $n,r\in\mathbb N$, let $o_1,o_2$ be Boolean query functions on subsets of $[n]$, and let a Boolean tape be indexed by $\mathbb N$. Fix an annealing schedule $s$, rational $q$, rational defect multipliers $w(i)$ indexed by ordered distinct empty/full pairs, and any initial restart cursor storing a paired state, tape position, and attempt count. For $m\in\mathbb N$, put $\ell_N(m)=\lfloor\log_2m\rfloor+1$, with $\log_2 0=0$. For a reduced rational $x$ with positive denominator, put $\ell_Q(x)=2+\ell_N(|\operatorname{num}(x)|)+\ell_N(\operatorname{den}(x))$. Let $K\in\mathbb N$ satisfy $$\ell_Q(1)+n\ell_Q(q)\le K,\qquad \ell_Q(w(i))\le K\quad\text{for all defect indices }i.$$ Put $A=s.\mathrm{restartCap}$ and $T=s.\mathrm{drawTrials}$, and define $$\begin{aligned}C(n,T,K)={}&2+3(3+T(3(4K+n+1)+2))\\&+4n(2n+3)+2(2n+1)+2(n(4n+3)+1)\\&+2(8(n+1)^3+(n+4)K^2+n^2+2)+16K^2+12K+5.\end{aligned}$$ Write $W(A)$ for the source's nonoracle charge of a computation $A$, namely fair-bit reads plus its named nonoracle instruction tallies. The capped positive-time trace-return procedure obeys $$W(\operatorname{traceReturn})\le A\bigl(C(n,T,K)+n(4n+3)+3\bigr).$$
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/RestartPhaseWork.lean#L21-L55

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
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
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

namespace CountingMatroid.Analysis.RestartPhaseWork
end CountingMatroid.Analysis.RestartPhaseWork
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
namespace CountingMatroid.Analysis.RestartPhaseWork
end CountingMatroid.Analysis.RestartPhaseWork
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RestartPhaseWork
open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines CountingMatroid.Program
open CountingMatroid.Analysis.ResourceBound
open CountingMatroid.Analysis.PhaseChainWork
open CountingMatroid.Analysis.BoundedRunResourceEnvelope
open CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

theorem CountingMatroid.Analysis.RestartPhaseWork.traceReturn_otherSteps_le {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (weights : Multipliers n)
    (start : RestartCursor n) (K : ℕ)
    (hq : binaryRatLength 1 + n * binaryRatLength q ≤ K)
    (hw : ∀ i, binaryRatLength (weights i) ≤ K) :
    otherSteps (traceReturn r o₁ o₂ tape s q weights start) ≤
      s.restartCap * (chainBudget n s.drawTrials K + n * (4 * n + 3) + 3) := by sorry
