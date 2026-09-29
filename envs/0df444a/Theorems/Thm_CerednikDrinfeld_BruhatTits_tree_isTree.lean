-- Prove2me | Theorems.Thm_CerednikDrinfeld_BruhatTits_tree_isTree
-- name    : CerednikDrinfeld.BruhatTits.tree_isTree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/3df28e0b-1797-5679-8e6f-6679f96ab49c
-- title:
--   The Bruhat–Tits lattice graph of GL₂ is a tree
-- statement:
--   Let $R$ be a commutative ring which is a domain and a discrete valuation ring, and let $K$ be a field equipped with an $R$-algebra structure making it the fraction field of $R$. The vertex type [`LT.LatticeTree.Vertex R K`](def/LatticeTreeOrbital.html#L349) is the quotient of the $R$-submodules $L$ of $K^2 = (\mathrm{Fin}\ 2 \to K)$ satisfying the predicate `IsFullLattice` by the homothety setoid, so a vertex is a homothety class $[L]$ of full lattices; the graph [`CerednikDrinfeld.BruhatTits.tree R K`](def/CerednikDrinfeld_BruhatTitsTree.html#L83) is obtained by `SimpleGraph.fromRel` from the relation `VertRel`, so two vertices $x$, $y$ are adjacent exactly when $x \neq y$ and, in one of the two orders, there are submodules $L, L'$ of $K^2$ with `IsFullLattice` holding for both, with homothety classes $x$ and $y$ respectively, such that the relation `AdjacentLattice L L'` holds. The assertion is that this graph satisfies Mathlib's `SimpleGraph.IsTree`, that is, it is connected (in particular its vertex type is nonempty) and acyclic: no vertex lies on a cycle.
--
--   This is the theorem of Serre that the Bruhat–Tits building of $\mathrm{SL}_2$, equivalently of $\mathrm{PGL}_2$, over a discretely valued field is a tree, here in the lattice-class model over a discrete valuation ring $R$ with fraction field $K$. It underlies the Čerednik–Drinfeld side of the development, where the tree and its quotients by discrete subgroups feed the Mumford uniformisation statements about $\mathrm{Pic}^0$ of the resulting curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_BruhatTits_tree_isTree.lean

import Definitions.Def_CerednikDrinfeld_BruhatTitsTree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.BruhatTits LT.LatticeTree

theorem CerednikDrinfeld.BruhatTits.tree_isTree
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] :
    (tree R K).IsTree := by sorry
