-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_NoPathSeparator_no_path_separator
-- name    : CountingMatroid.Analysis.NoPathSeparator.no_path_separator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:08:24.453304+00:00
-- url     : https://prove2.me/theorems/440fe3bd-3b89-4465-a1a9-47f7a101e941
-- title:
--   An unsuccessful capped graph search supplies a directed separator
-- statement:
--   Let $n\in\mathbb N$ and let $G$ be a directed graph on $\{0,\ldots,n-1\}$ with Boolean edge relation and Boolean source and target flags at each vertex. Let $\operatorname{findPath}(G)$ be the program's synchronous search using $n$ reachability-expansion rounds. If it returns no path, there exists a subset $R$ such that $$\{\text{sources}\}\subseteq R,\qquad u\in R,\ u\to v\Longrightarrow v\in R,\qquad R\cap\{\text{targets}\}=\varnothing.$$
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/NoPathSeparator.lean#L16-L162

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

namespace CountingMatroid.Analysis.NoPathSeparator
end CountingMatroid.Analysis.NoPathSeparator
namespace Arlib
end Arlib
set_option autoImplicit false

/-!
Graph-theoretic correctness of the capped synchronous search in
`IntersectionSearch`. The separator is a set of vertices containing every
source, closed under directed edges, and containing no sink. This file does
not use matroid axioms or assume a mathematical intersection algorithm.
-/

namespace CountingMatroid.Analysis.NoPathSeparator
end CountingMatroid.Analysis.NoPathSeparator
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.NoPathSeparator

open CountingMatroid.Analysis.IntersectionSearch

theorem CountingMatroid.Analysis.NoPathSeparator.no_path_separator {n : ℕ} (g : ExchangeGraph n)
    (hnone : (findPath g).val = none) :
    ∃ R : Finset (Fin n),
      (∀ i, (g.terminals i).1 = true → i ∈ R) ∧
      (∀ u v, u ∈ R → g.edges u v = true → v ∈ R) ∧
      (∀ i, i ∈ R → (g.terminals i).2 = false) := by sorry
