-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_ResourceBound_acceptance_oracleCalls_zero
-- name    : CountingMatroid.Analysis.ResourceBound.acceptance_oracleCalls_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T12:53:02.52416+00:00
-- url     : https://prove2.me/theorems/2f31c0cb-249b-4533-a65f-ff72f406527e
-- title:
--   The acceptance-comparison block uses no independence queries
-- statement:
--   Let $S,S'\subseteq[n]\times\{0,1\}$ be the current and candidate states, let $w,w'\in\mathbb Q$ be their supplied weights, let $b:\mathbb N\to\{0,1\}$ be a tape, and let $T,c\in\mathbb N$ be a draw-trial cap and cursor. Define the acceptance block by forming $\theta=w'/w$ using total rational division. If $\theta\ge1$, return $S'$ at cursor $c$. Otherwise run the capped uniform draw below $\operatorname{den}(\theta)$; propagate failure, or compare its value with $|\operatorname{num}(\theta)|$ and return $S'$ if smaller and $S$ otherwise, with the draw's cursor. Then $$\operatorname{oracleCalls}(\text{acceptance block})=0.$$
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/PrimitiveOracleCalls.lean#L333-L375

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
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Program
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
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
set_option autoImplicit false

namespace CountingMatroid.Analysis.ResourceBound
end CountingMatroid.Analysis.ResourceBound
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ResourceBound

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines
open CountingMatroid.Model.Operations

theorem CountingMatroid.Analysis.ResourceBound.acceptance_oracleCalls_zero {n : ℕ} (tape : ℕ → Bool)
    (drawTrials : ℕ) (oldWeight newWeight : ℚ)
    (state candidate : PairedSet n) (cursor : ℕ) :
    oracleCalls (do
      let ratio ← ratDiv newWeight oldWeight
      let needsDraw ← ratLess ratio 1
      if needsDraw then
        let denominator ← rationalDenominator ratio
        let numerator ← rationalNumerator ratio
        let acceptedDraw ← CountingMatroid.Program.boundedUniform tape drawTrials
          denominator cursor
        match acceptedDraw.1 with
        | none => pure none
        | some value =>
            let accepted ← lessThan value numerator
            if accepted then pure (some (candidate, acceptedDraw.2))
            else pure (some (state, acceptedDraw.2))
      else pure (some (candidate, cursor))) = 0 := by sorry
