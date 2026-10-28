-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_IntersectionSearchCost_cost_findPath_le
-- name    : CountingMatroid.Analysis.IntersectionSearchCost.cost_findPath_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:41:13.278582+00:00
-- url     : https://prove2.me/theorems/7c2b98ff-d2fd-4db8-beef-b05a3e30509b
-- title:
--   Quintic charged-cost bound for bounded path search
-- statement:
--   For a charged computation $A$, write $c_{\mathrm{op}}(A)$ for its natural-number cost in operation category $\mathrm{op}$. These are abstract charged-operation counters; no concrete physical-bit implementation is asserted. Let $n\in\mathbb N$ and let $g$ be any directed graph on $[n]$ with source and sink flags. The routine $\mathrm{findPath}(g)$ initializes source paths, performs $n$ frozen breadth-first layers with lists capped at $n$ entries, and selects a shortest recorded sink path. For every operation category,
--
--   $$c_{\mathrm{op}}(\mathrm{findPath}(g))\le30(n+1)^5.$$
--
--   The graph need not arise from matroid oracles.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/IntersectionSearchCost.lean#L165-L193

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Cost_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Machine_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroid_Analysis_IntersectionSearch
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

namespace CountingMatroid.Analysis.IntersectionSearchCost
end CountingMatroid.Analysis.IntersectionSearchCost
namespace Arlib
end Arlib
set_option autoImplicit false

/-!
Uniform resource obligation for the concrete capped exchange-graph solver.
The proved bound composes table and fold accounting through graph construction,
frozen breadth-first layers, sink selection, and at most `n` toggles, then
through the `r`-round solver.
It is independent of all matroid and exact-oracle promises.
-/

namespace CountingMatroid.Analysis.IntersectionSearchCost
end CountingMatroid.Analysis.IntersectionSearchCost
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.IntersectionSearchCost

open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines
open CountingMatroid.Analysis.IntersectionSearch

theorem CountingMatroid.Analysis.IntersectionSearchCost.cost_findPath_le {n : ℕ} (g : ExchangeGraph n) (op : Op) :
    (findPath g).cost op ≤ 30 * (n + 1) ^ 5 := by sorry
