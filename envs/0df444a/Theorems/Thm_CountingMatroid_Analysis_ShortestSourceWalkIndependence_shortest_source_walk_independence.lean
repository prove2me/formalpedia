-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_ShortestSourceWalkIndependence_shortest_source_walk_independence
-- name    : CountingMatroid.Analysis.ShortestSourceWalkIndependence.shortest_source_walk_independence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:07:03.340956+00:00
-- url     : https://prove2.me/theorems/35823cd4-0e76-4df1-9183-2f3538fb181a
-- title:
--   Shortest source walks preserve matroid independence
-- statement:
--   Let $M$ be a matroid with full ground set $[n]$, let $I\subseteq[n]$ be independent, and let $g$ be a Boolean directed graph with designated sources. Assume a vertex $v$ is a source exactly when $v\notin I$ and $I\cup\{v\}$ is independent. Assume every edge joins an inside vertex to an outside vertex in one direction or the other. Finally, for $u\in I$ and $v\notin I$, require
--   $$u\to v\quad\Longleftrightarrow\quad (I\setminus\{u\})\cup\{v\}\text{ is independent in }M.$$
--   Let $p$ be a nonempty source walk stored in reverse order, with its endpoint at the head and its source last. Suppose $p$ has no repeated vertices and is shortest among all source walks with that same head endpoint. Put $J=I\triangle\operatorname{set}(p)$. Then
--   $$J\text{ is independent in }M,$$
--   and if the head vertex $v$ belongs to the original set $I$, then
--   $$J\cup\{v\}\text{ is independent in }M.$$
--   This strengthened independence statement supplies the single-matroid induction behind shortest-path augmentation.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ShortestSourceWalkIndependence.lean#L63-L219

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

theorem CountingMatroid.Analysis.ShortestSourceWalkIndependence.shortest_source_walk_independence {n : ℕ} (M : Matroid (Fin n))
    (g : ExchangeGraph n) (I : Finset (Fin n)) (hE : M.E = Set.univ)
    (hI : M.Indep (I : Set (Fin n)))
    (hsrc : ∀ v, (g.terminals v).1 = true ↔
      v ∉ I ∧ M.Indep (insert v (I : Set (Fin n))))
    (halt : ∀ u v, g.edges u v = true →
      (u ∈ I ∧ v ∉ I) ∨ (u ∉ I ∧ v ∈ I))
    (hexch : ∀ u v, u ∈ I → v ∉ I →
      (g.edges u v = true ↔ M.Indep (insert v (↑(I.erase u) : Set (Fin n)))))
    (p : List (Fin n)) (hw : SourceWalk g p) (hp : p.Nodup)
    (hmin : ∀ v tail, p = v :: tail → ∀ q, SourceWalk g (v :: q) →
      p.length ≤ (v :: q).length) :
    M.Indep (↑(I ∆ p.toFinset) : Set (Fin n)) ∧
      ∀ v tail, p = v :: tail → v ∈ I →
        M.Indep (insert v (↑(I ∆ p.toFinset) : Set (Fin n))) := by sorry
