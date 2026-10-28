-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_ShortestSourceWalkIndependence_walk_suffix_length
-- name    : CountingMatroid.Analysis.ShortestSourceWalkIndependence.walk_suffix_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:51:04.00116+00:00
-- url     : https://prove2.me/theorems/452033b1-beca-409e-9cc2-8f4120e5bc66
-- title:
--   Every vertex of a reverse source walk begins a shorter source-walk suffix
-- statement:
--   Let $n\in\mathbb N$, and let $G$ be a directed graph on $[n]$ equipped with source and sink flags, as represented by an exchange graph. A source walk is a nonempty reverse list: its last vertex is a flagged source, and each successive step toward its head follows a directed edge. Let $p$ be such a source walk. For every vertex $v$ occurring in $p$, there exists a list $q$ such that
--   $$v::q\text{ is a source walk in }G,\qquad |v::q|\le|p|.$$
--   No simplicity or shortestness assumption is required.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ShortestSourceWalkIndependence.lean#L14-L30

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
import Mathlib.Data.Finset.SymmDiff
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

namespace CountingMatroid.Analysis.ShortestSourceWalkIndependence
end CountingMatroid.Analysis.ShortestSourceWalkIndependence
namespace Arlib
end Arlib
set_option autoImplicit false

/-! The first-matroid half of shortest-path augmentation. Fundamental circuits
of later outside vertices avoid all earlier removed inside vertices, since such
membership would give a shorter source walk. -/
namespace CountingMatroid.Analysis.ShortestSourceWalkIndependence
end CountingMatroid.Analysis.ShortestSourceWalkIndependence
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ShortestSourceWalkIndependence
open CountingMatroid.Model CountingMatroid.Analysis.IntersectionSearch
open CountingMatroid.Analysis.ExchangePathCertificate
open scoped symmDiff

theorem CountingMatroid.Analysis.ShortestSourceWalkIndependence.walk_suffix_length {n : ℕ} {g : ExchangeGraph n} {p : List (Fin n)}
    (hw : SourceWalk g p) : ∀ v ∈ p, ∃ q, SourceWalk g (v :: q) ∧
      (v :: q).length ≤ p.length := by sorry
