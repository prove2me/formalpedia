-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_IntersectionSearchCost_cost_tabulate_le
-- name    : CountingMatroid.Analysis.IntersectionSearchCost.cost_tabulate_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:52:01.332169+00:00
-- url     : https://prove2.me/theorems/8df53617-3a2c-4a6c-90be-13529b1d7625
-- title:
--   Coordinatewise charged-cost bound for tabulation
-- statement:
--   For a charged computation $A$, write $c_{\mathrm{op}}(A)$ for its natural-number cost in operation category $\mathrm{op}$. These are abstract charged-operation counters; no concrete physical-bit implementation is asserted. Let $n,w,k\in\mathbb N$, let $\alpha$ have a default element, and let $f(i)$ be an $\alpha$-valued charged computation for each $i\in[n]$. Suppose
--   $$c_{\mathrm{op}}(f(i))\le k\qquad\text{for all }i,\mathrm{op}.$$
--   Then every operation category satisfies
--
--   $$c_{\mathrm{op}}(\mathrm{tabulate}(w,f))
--   \le nw+1+n\bigl(k+(nw+1)\bigr).$$
--
--   The width $w$ controls the table allocation and overwrite charges.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/IntersectionSearchCost.lean#L42-L64

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

theorem CountingMatroid.Analysis.IntersectionSearchCost.cost_tabulate_le {n : ℕ} {α : Type} [Inhabited α]
    (width k : ℕ) (f : Fin n → Arlib.Computation.Charged Op Cell α)
    (hf : ∀ i op, (f i).cost op ≤ k) (op : Op) :
    (tabulate width f).cost op ≤
      (n * width + 1) + n * (k + (n * width + 1)) := by sorry
