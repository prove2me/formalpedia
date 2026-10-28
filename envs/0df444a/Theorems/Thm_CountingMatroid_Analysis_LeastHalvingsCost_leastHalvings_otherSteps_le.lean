-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_LeastHalvingsCost_leastHalvings_otherSteps_le
-- name    : CountingMatroid.Analysis.LeastHalvingsCost.leastHalvings_otherSteps_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T11:55:49.804268+00:00
-- url     : https://prove2.me/theorems/4403738d-6f8a-497c-a512-304c207f10d1
-- title:
--   Charged work of the capped halving search
-- statement:
--   For a rational number $q=a/b$ in reduced form with $b>0$, define $\lambda(m)=\lfloor\log_2 m\rfloor+1$ for positive integers and $\lambda(0)=1$, and let $\ell(q)=2+\lambda(|a|)+\lambda(b)$. The routine $\operatorname{leastHalvings}(q)$ starts with $1$ and repeatedly halves while $q$ is smaller, with cap $\lfloor\log_2 b\rfloor+8$. Its abstract nonoracle charged work satisfies $$\operatorname{otherSteps}(\operatorname{leastHalvings}(q))\le100(\lfloor\log_2 b\rfloor+8)\bigl(\ell(q)+\lfloor\log_2 b\rfloor+16\bigr)^2+1.$$ This bound holds for every rational $q$.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/LeastHalvingsCost.lean#L26-L169

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
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

namespace CountingMatroid.Analysis.ResourceBound
end CountingMatroid.Analysis.ResourceBound
set_option autoImplicit false

namespace CountingMatroid.Analysis.LeastHalvingsCost
end CountingMatroid.Analysis.LeastHalvingsCost
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.LeastHalvingsCost

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines
open CountingMatroid.Model.Operations
open CountingMatroid.Analysis.ResourceBound

theorem CountingMatroid.Analysis.LeastHalvingsCost.leastHalvings_otherSteps_le (q : ℚ) :
    otherSteps (CountingMatroid.Program.leastHalvings q) ≤
      100 * (q.den.log2 + 8) *
        (binaryRatLength q + q.den.log2 + 16) ^ 2 + 1 := by sorry
