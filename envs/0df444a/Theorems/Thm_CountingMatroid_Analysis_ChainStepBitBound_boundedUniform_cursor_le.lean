-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_ChainStepBitBound_boundedUniform_cursor_le
-- name    : CountingMatroid.Analysis.ChainStepBitBound.boundedUniform_cursor_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:06:50.377365+00:00
-- url     : https://prove2.me/theorems/d7f15073-0a1b-4b48-ad22-4b6b7dbb9a4a
-- title:
--   A capped uniform draw has bounded tape consumption
-- statement:
--   Let $\omega:\mathbb N\to\{0,1\}$ be any Boolean tape and let $T,v,c\in\mathbb N$. Write $b$ for the final cursor of the bounded uniform sampler with at most $T$ rejection trials, range bound $v$, and initial cursor $c$. Put $\ell(v)=\operatorname{log2}(v\mathbin{\dot-}1)+1$, where $\dot-$ is truncated natural subtraction and $\operatorname{log2}(0)=0$. Then
--
--   $$b\le c+T\ell(v).$$
--
--   The bound also applies when the sampler aborts. It bounds tape positions consumed, not the cost of a concrete machine implementation.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ChainStepBitBound.lean#L27-L65

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
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformReplay
import Definitions.Def_CountingMatroid_Analysis_ChainDrawSiteReplay
import Definitions.Def_CountingMatroid_Analysis_ChainStepIntervalReplay
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

namespace CountingMatroid.Analysis.ChainStepBitBound
end CountingMatroid.Analysis.ChainStepBitBound
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
namespace CountingMatroid.Analysis.LeastHalvingsCost
end CountingMatroid.Analysis.LeastHalvingsCost
namespace CountingMatroid.Analysis
end CountingMatroid.Analysis
set_option autoImplicit false

namespace CountingMatroid.Analysis.ChainStepBitBound
end CountingMatroid.Analysis.ChainStepBitBound
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ChainStepBitBound

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
open CountingMatroid.Analysis.ObservationRoundDrawSites

theorem CountingMatroid.Analysis.ChainStepBitBound.boundedUniform_cursor_le (tape : ℕ → Bool) (trials v cursor : ℕ) :
    (boundedUniform tape trials v cursor).val.2 ≤
      cursor + trials * ((v - 1).log2 + 1) := by sorry
