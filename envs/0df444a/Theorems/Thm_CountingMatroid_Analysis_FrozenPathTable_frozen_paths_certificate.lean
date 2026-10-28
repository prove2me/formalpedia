-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_FrozenPathTable_frozen_paths_certificate
-- name    : CountingMatroid.Analysis.FrozenPathTable.frozen_paths_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:08:26.948216+00:00
-- url     : https://prove2.me/theorems/a07df7ba-9578-4596-945d-1a6e46274256
-- title:
--   Certificate for the completed frozen breadth-first path table
-- statement:
--   Let $g$ be any directed graph on $[n]$ equipped with Boolean source and sink flags. Initialize each source with its singleton reverse path and all other entries as absent. Perform $n$ synchronous relaxation layers, each using only the previous table, retaining already discovered paths and capping new lists at $n$ vertices. Let $P(v)$ be the final optional path at $v$. A reverse source walk lists its endpoint first, follows directed edges in reverse list order, and ends at a source.
--
--   Then every stored path is a simple reverse source walk with its indexed endpoint, and every source walk with at most $n$ vertices has a recorded competitor no longer than itself:
--
--   $$\begin{aligned}
--   P(v)=p&\implies p=(v,\ldots),\ p\text{ is a source walk},\
--   p\text{ has no repeated vertices},\ |p|\le n;\\
--   (v,\ldots)\text{ a source walk},\ \ell\le n
--   &\implies\exists p:\ P(v)=p,\ |p|\le\ell.
--   \end{aligned}$$
--
--   This justifies the representation cap used by the search.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/FrozenPathTable.lean#L13-L213

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Cost_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Machine_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroid_Analysis_ExchangePathCertificate
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

namespace CountingMatroid.Analysis.FrozenPathTable
end CountingMatroid.Analysis.FrozenPathTable
namespace Arlib
end Arlib
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! The frozen BFS table certificate, before the final sink selection.
First discovery and bounded-distance completeness establish simple, globally
shortest recorded source walks. Thus the representation cap discards no vertex. -/
namespace CountingMatroid.Analysis.FrozenPathTable
end CountingMatroid.Analysis.FrozenPathTable
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.FrozenPathTable
open CountingMatroid.Analysis.IntersectionSearch
open CountingMatroid.Analysis.ExchangePathCertificate

theorem CountingMatroid.Analysis.FrozenPathTable.frozen_paths_certificate {n : ℕ} (g : ExchangeGraph n) :
    let paths := (Arlib.Computation.Charged.foldl
      (fun paths (_ : ℕ) => relaxPaths g paths) (List.range n)
      (initialPaths g).val).val
    (∀ v p, paths v = some p →
      SourceWalk g p ∧ (∃ tail, p = v :: tail) ∧ p.Nodup ∧ p.length ≤ n) ∧
    (∀ v tail, SourceWalk g (v :: tail) → (v :: tail).length ≤ n →
      ∃ p, paths v = some p ∧ p.length ≤ (v :: tail).length) := by sorry
