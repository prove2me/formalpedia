-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_FindPathCertificate_findPath_certificate
-- name    : CountingMatroid.Analysis.FindPathCertificate.findPath_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:40:39.979607+00:00
-- url     : https://prove2.me/theorems/b2f273f0-da57-479b-8048-2755e5b87912
-- title:
--   Every path returned by the search has a shortest-path certificate
-- statement:
--   Let $n\in\mathbb N$ and let $g$ be any directed graph on $[n]$ with designated source and sink flags. If its frozen-layer path-search routine returns a vertex list $p$, then $p$ is a reverse source-to-sink walk, its entries are distinct, and
--
--   $$|p|\le n,\qquad |p|\le|q|\quad\text{for every reverse source-to-sink walk }q\text{ in }g.$$
--
--   In this representation the last vertex is a source, the first is a sink, and edges are followed from right to left. Minimality is over all such walks, not merely those explicitly stored by the search.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/FindPathCertificate.lean#L14-L189

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

namespace CountingMatroid.Analysis.FindPathCertificate
end CountingMatroid.Analysis.FindPathCertificate
namespace CountingMatroid.Analysis.FrozenPathTable
end CountingMatroid.Analysis.FrozenPathTable
namespace Arlib
end Arlib
set_option autoImplicit false

/-! Algorithmic half of successful augmentation, independent of matroid axioms.
The frozen BFS table certificate supplies valid simple source walks and
bounded-distance optimality. The final sink fold preserves validity and
selects a globally shortest source-to-sink walk. Both list caps are harmless. -/
namespace CountingMatroid.Analysis.FindPathCertificate
end CountingMatroid.Analysis.FindPathCertificate
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.FindPathCertificate
open CountingMatroid.Analysis.IntersectionSearch
open CountingMatroid.Analysis.ExchangePathCertificate

theorem CountingMatroid.Analysis.FindPathCertificate.findPath_certificate {n : ℕ} (g : ExchangeGraph n) (p : List (Fin n))
    (hp : (findPath g).val = some p) : ShortestCertificate g p := by sorry
