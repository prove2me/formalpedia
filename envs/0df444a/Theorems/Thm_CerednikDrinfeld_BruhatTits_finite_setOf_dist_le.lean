-- Prove2me | Theorems.Thm_CerednikDrinfeld_BruhatTits_finite_setOf_dist_le
-- name    : CerednikDrinfeld.BruhatTits.finite_setOf_dist_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/8b73fa05-091d-5f09-9b36-d66f685fe160
-- title:
--   Finiteness of balls in the Bruhat–Tits tree
-- statement:
--   Let $R$ be a discrete valuation ring that is a domain, $K$ a field which is the fraction field of $R$ (via a given $R$-algebra structure), and let $\varpi \in R$ be an irreducible element whose residue ring $R/(\varpi)$ is finite. Let $v$ be a vertex of the lattice tree, i.e. an element of [`LT.LatticeTree.Vertex R K`](def/LatticeTreeOrbital.html#L349), the quotient of the full $R$-lattices in $K^2 = (\mathrm{Fin}\ 2 \to K)$ by the equivalence relation of homothety, and let $d$ be a natural number. The graph in question is [`CerednikDrinfeld.BruhatTits.tree R K`](def/CerednikDrinfeld_BruhatTitsTree.html#L83), obtained by symmetrising the relation `VertRel R K` on vertices, where two classes $x, y$ are related when they admit representatives, full lattices $L$ and $L'$, satisfying the predicate `AdjacentLattice L L'`. The assertion is that the set of vertices $w$ with $\mathrm{dist}(v,w) \le d$ in this graph is finite, the distance being Mathlib's graph distance (which takes the value $0$ on pairs of vertices lying in different connected components, so that the set in question contains all vertices not joinable to $v$).
--
--   This is the local finiteness of the Bruhat–Tits tree of $\mathrm{GL}_2$ over a discrete valuation ring with finite residue field, in the form 'metric balls are finite'. It is used in the study of the tree's quotients and stabilisers, for instance to deduce finiteness of a quotient graph's edges from finiteness of its vertices, finiteness of vertex stabilisers from finiteness of dart stabilisers, and the existence of a uniform exponent killing stabiliser elements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_BruhatTits_finite_setOf_dist_le.lean

import Definitions.Def_LatticeTreeBaseChange
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open LT.LatticeTree

theorem CerednikDrinfeld.BruhatTits.finite_setOf_dist_le
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (v : LT.LatticeTree.Vertex R K) (d : ℕ) :
    ({w : LT.LatticeTree.Vertex R K | (CerednikDrinfeld.BruhatTits.tree R K).dist v w ≤ d}).Finite := by sorry
