-- Prove2me | Theorems.Thm_CerednikDrinfeld_BruhatTits_tree_connected_and_colorable_two
-- name    : CerednikDrinfeld.BruhatTits.tree_connected_and_colorable_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/c250420b-8145-532a-84f4-3ca4aaea6d36
-- title:
--   Connectedness and bipartiteness of the Bruhat–Tits lattice graph
-- statement:
--   Let $R$ be a commutative ring which is a domain and a discrete valuation ring, and let $K$ be a field equipped with an $R$-algebra structure making it the fraction field of $R$. Consider the vertex type `Vertex R K`, the quotient of the $R$-submodules of $K^2$ (written $\mathrm{Fin}\,2 \to K$) satisfying the predicate `IsFullLattice` by the homothety setoid, and the relation `VertRel R K` which holds of two classes $x,y$ when there are full lattices $L, L'$ with classes $x$ and $y$ respectively such that `AdjacentLattice L L'` holds. The graph `tree R K` is the simple graph on `Vertex R K` obtained from this relation by symmetrisation and removal of loops, so that $x$ and $y$ are adjacent exactly when $x \neq y$ and `VertRel R K` holds in one of the two orders. The assertion is the conjunction of two statements: `tree R K` is connected (nonempty, with any two vertices joined by a walk), and it admits a colouring with $2$ colours, i.e. it is bipartite.
--
--   This is the graph-theoretic half of the classical description of the Bruhat–Tits tree of $\mathrm{PGL}_2(K)$ for a discretely valued field, as in Serre's account: vertices are homothety classes of full lattices in $K^2$, adjacency is the elementary-divisor condition, and the two colours record the parity of the vertex type; acyclicity is not part of the present assertion. It underlies the combinatorial input to the Mumford-curve and Čerednik–Drinfeld constructions, and is invoked by the statements on equivariant uniformisations and theta-quotients of Mumford curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_BruhatTits_tree_connected_and_colorable_two.lean

import Definitions.Def_CerednikDrinfeld_BruhatTitsTree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.BruhatTits LT.LatticeTree

theorem CerednikDrinfeld.BruhatTits.tree_connected_and_colorable_two
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] :
    (tree R K).Connected ∧ (tree R K).Colorable 2 := by sorry
