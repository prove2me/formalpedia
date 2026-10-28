-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_RankOneFeasibility_singletonScan_costs
-- name    : CountingMatroid.Analysis.RankOneFeasibility.singletonScan_costs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:52:20.907253+00:00
-- url     : https://prove2.me/theorems/854513c5-2513-4b5d-a3cb-a6005b3f227d
-- title:
--   Exact resource counts for the singleton scan
-- statement:
--   Let $n\in\mathbb N$ and let $o_1,o_2$ be arbitrary Boolean query functions on subsets of $[n]$. Let $A$ be the charged singleton scan, which queries both functions for every singleton without early termination. Then $$\operatorname{oracleCalls}(A)=2n,\qquad \operatorname{otherSteps}(A)=n\bigl(n(n+1)+3\bigr).$$ Here oracleCalls adds the two original oracle counters, and otherSteps sums fair-bit reads and the charged named nonoracle instructions.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/RankOneFeasibility.lean#L91-L125

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Cost_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Machine_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroid_Analysis_RankOneFeasibility
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Subroutines
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF

namespace Arlib
end Arlib
set_option autoImplicit false

/-!
The first augmentation from the empty common independent set can be found by
scanning singleton queries. This file implements that scan through the two
original charged oracles. It handles rank one, including infeasible inputs;
it does not implement subsequent augmentations for larger ranks.
-/

namespace CountingMatroid.Analysis.RankOneFeasibility
end CountingMatroid.Analysis.RankOneFeasibility
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RankOneFeasibility

open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines
open scoped Classical

theorem CountingMatroid.Analysis.RankOneFeasibility.singletonScan_costs {n : ℕ} (o₁ o₂ : IndependenceOracle n) :
    oracleCalls (singletonScan o₁ o₂) = 2 * n ∧
      otherSteps (singletonScan o₁ o₂) = n * (n * (n + 1) + 3) := by sorry
