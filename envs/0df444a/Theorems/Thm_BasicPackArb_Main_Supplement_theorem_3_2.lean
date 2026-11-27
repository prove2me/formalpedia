-- Prove2me | Theorems.Thm_BasicPackArb_Main_Supplement_theorem_3_2
-- name    : BasicPackArb.Main.Supplement.theorem_3_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T10:01:54.331854+00:00
-- url     : https://prove2.me/theorems/b8a31c57-bdbc-439a-a524-e32c327d1739
-- title:
--   Theorem 3.2 — nonemptiness, integrality and exact vertices of the packing polyhedron
-- statement:
--   Let $D=(V,A)$ be a finite digraph with root placement $\pi:S\to V$ and matroid $M$ on $S$, of rank $k$. For $x\in\mathbb R^A$, write $x(F)=\sum_{a\in F}x(a)$ and let $P_{M,D}$ be defined by
--
--   $$0\le x(a)\le1\ (a\in A),\qquad x(\varrho_D(X))+r_M(S_X)\ge k\ (\varnothing\ne X\subseteq V),\qquad x(A)=k|V|-|S|.$$
--
--   Then
--
--   $$\text{an }M\text{-basic arborescence packing exists}\quad\Longleftrightarrow\quad P_{M,D}\ne\varnothing.$$
--
--   When this polyhedron is nonempty, it is integral, and its extreme points are exactly the characteristic vectors of the arc unions of all $M$-basic arborescence packings. Both inclusions in this exact equality are asserted. No independence or connectedness premise is supplied; those conditions follow from nonemptiness. This result describes the full convex hull needed for cost optimization.
--
--   **Formalization Note** The total-size equality is real arithmetic. Loops are retained as coordinates; on a feasible face they are forced to zero. The p. 6 proof's singleton-cut sum is a sum over nonloop arcs, so its equality with $x(A)$ is replaced by the valid inequality for loops, without changing the theorem.
--
--   Differences from the source:
--   - encoding: finite graphs, root sets and matroids on S → finite vertex/root carriers, finite edge sets with edge identities, and M.E = Set.univ; reason: these presentations include every source instance, preserve parallel edges and repeated roots, and express that the ground set is exactly S
--   - encoding: real vectors indexed by A and an integer polyhedron → functions on the subtype of actual arcs and equality with the convex hull of integer points; reason: there are no free coordinates for unused ambient arcs, and bounded polyhedra are integral exactly in this convex-hull sense
--   - encoding: k minus r_M(S_X) and k|V| minus |S| → additive real cut inequalities and the untruncated real total-size equality; reason: finite rank conversion and rearrangement preserve both infeasibility and every boundary case
-- source:
--   Durand de Gevigney, Nguyen, Szigeti, Basic Packing of Arborescences, arXiv:1207.1985v1, p. 6, Theorem 3.2

import Definitions.Def_BasicPackArb_Main_Supplement_Polyhedron

set_option autoImplicit false

namespace BasicPackArb.Main.Supplement

/-- Theorem 3.2, p. 6: existence, integrality and the exact extreme-point set. -/
theorem theorem_3_2 {V Arc S : Type} [Fintype V] [Fintype S]
    [DecidableEq V] (D : Digraph V Arc) (π : S → V)
    (M : Matroid S) (hground : M.E = Set.univ) :
    ((∃ T : S → Arborescence D, IsBasicPacking D π M T) ↔
      (packingPolyhedron D π M).Nonempty) ∧
    ((packingPolyhedron D π M).Nonempty →
      IntegralPolyhedron (packingPolyhedron D π M) ∧
      (packingPolyhedron D π M).extremePoints ℝ =
        {x | ∃ T : S → Arborescence D, IsBasicPacking D π M T ∧ x = packingVector D T}) := by sorry

end BasicPackArb.Main.Supplement
