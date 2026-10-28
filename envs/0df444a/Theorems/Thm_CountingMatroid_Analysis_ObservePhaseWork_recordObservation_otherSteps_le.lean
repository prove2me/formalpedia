-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_ObservePhaseWork_recordObservation_otherSteps_le
-- name    : CountingMatroid.Analysis.ObservePhaseWork.recordObservation_otherSteps_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T12:56:22.447411+00:00
-- url     : https://prove2.me/theorems/ccb71838-82d1-431f-bc7d-9710460b9b19
-- title:
--   Charged work of recording one height-bounded observation
-- statement:
--   Let $n,r\in\mathbb N$, let $o_1,o_2$ be arbitrary Boolean subset oracles, let $\rho\in\mathbb Q$, and let $O$ be an observation record containing a paired subset, bit cursor, class counts, and rational numerator sum $a/b$ in reduced form with $b>0$. Define its rational height by $h(a/b)=1+\max\{\log_2|a|,\log_2 b\}$, where logarithms are natural-number floor logarithms and $\log_2 0=0$. Let $H\in\mathbb N$ satisfy $h(O.\mathrm{numeratorSum})\le H$. Put $R=\ell(\rho)$, where $\ell(a/b)=2+(\log_2|a|+1)+(\log_2 b+1)$. Then $$\operatorname{otherSteps}(\operatorname{recordObservation}(r,o_1,o_2,\rho,O))\le B(n,R,H),$$ where $$\begin{aligned}B(n,R,H)={}&n(4n+3)+1+3(n^2+2)+8(n+1)^3+1\\&+n(4+nR)^2+(2H+2+4+nR)^2.\end{aligned}$$
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ObservePhaseWork.lean#L19-L58

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
import Definitions.Def_CountingMatroid_Analysis_ObservePhaseWork
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
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

namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope
end CountingMatroid.Analysis.BoundedRunResourceEnvelope
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
namespace CountingMatroid.Analysis.ObservePhaseWork
end CountingMatroid.Analysis.ObservePhaseWork
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ObservePhaseWork
open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines CountingMatroid.Program
open CountingMatroid.Analysis.ResourceBound
open CountingMatroid.Analysis.PhaseChainWork
open CountingMatroid.Analysis.BoundedRunResourceEnvelope
open CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
open CountingMatroid.Analysis.RationalHeight

theorem CountingMatroid.Analysis.ObservePhaseWork.recordObservation_otherSteps_le {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (rho : ℚ) (current : ObservationCursor n)
    (H : ℕ) (hh : rationalHeight current.numeratorSum ≤ H) :
    otherSteps (recordObservation r o₁ o₂ rho current) ≤
      recordBudget n (binaryRatLength rho) H := by sorry
