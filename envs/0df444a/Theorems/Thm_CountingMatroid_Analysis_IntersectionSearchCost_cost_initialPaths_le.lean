-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_IntersectionSearchCost_cost_initialPaths_le
-- name    : CountingMatroid.Analysis.IntersectionSearchCost.cost_initialPaths_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:08:22.717987+00:00
-- url     : https://prove2.me/theorems/d032a436-f8fe-4e1e-8b3e-20a847cc9e37
-- title:
--   Initializing exchange-search paths has a cubic bound in each charge coordinate
-- statement:
--   Let $n\in\mathbb N$ and let $G$ be any exchange-graph record on $[n]$, with source/sink flags and directed-edge flags. The initialization routine constructs a table assigning the singleton list $[i]$ to each flagged source $i$ and no path to other vertices. For every modeled operation category $a$, its charge satisfies
--   $$\operatorname{cost}_a(\operatorname{initialPaths}(G))\le10(n+1)^3.$$
--   The graph need not arise from matroid oracles.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/IntersectionSearchCost.lean#L140-L155

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

theorem CountingMatroid.Analysis.IntersectionSearchCost.cost_initialPaths_le {n : ℕ} (g : ExchangeGraph n) (op : Op) :
    (initialPaths g).cost op ≤ 10 * (n + 1) ^ 3 := by sorry
