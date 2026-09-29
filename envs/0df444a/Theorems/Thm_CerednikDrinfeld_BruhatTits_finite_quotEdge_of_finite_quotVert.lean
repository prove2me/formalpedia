-- Prove2me | Theorems.Thm_CerednikDrinfeld_BruhatTits_finite_quotEdge_of_finite_quotVert
-- name    : CerednikDrinfeld.BruhatTits.finite_quotEdge_of_finite_quotVert
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/9fcffdd3-fe71-54d3-9259-f7b08411bf90
-- title:
--   Finitely many vertex orbits implies finitely many dart orbits
-- statement:
--   Let $R$ be a commutative domain which is a discrete valuation ring, $K_0$ a field equipped with an $R$-algebra structure making it the fraction field of $R$, and let $\varpi \in R$ be an irreducible element such that the quotient $R/(\varpi)$ is finite. Write $\mathrm{Vertex}\,R\,K_0$ for the set of homothety classes of full $R$-lattices in $K_0^2$, and let $\mathcal{T} =$ [`CerednikDrinfeld.BruhatTits.tree`](def/CerednikDrinfeld_BruhatTitsTree.html#L83) $R\,K_0$ be the simple graph on this set obtained by symmetrising the relation `VertRel`, which holds of two classes $x,y$ when they are represented by full lattices $L, L'$ with `AdjacentLattice` $L\,L'$. Let $G$ be a group acting on $\mathrm{Vertex}\,R\,K_0$ such that the action preserves adjacency in $\mathcal{T}$, i.e. $g \cdot v$ is adjacent to $g \cdot w$ whenever $v$ is adjacent to $w$ (the `GraphAction` condition). Assume the orbit quotient of $G$ on $\mathrm{Vertex}\,R\,K_0$ is finite. Then the orbit quotient of $G$ on the set of darts of $\mathcal{T}$ — ordered pairs of adjacent vertices, with the induced $G$-action — is finite.
--
--   This is the standard passage from finiteness of the vertex quotient to finiteness of the oriented edge quotient for a group acting on the Bruhat–Tits tree of $\mathrm{SL}_2$ over a local field with finite residue field, the finiteness resting on local finiteness of the tree. It supplies the finiteness of the set of dart orbits needed in the treatment of tree lattices and Mumford-period constructions on the Čerednik–Drinfeld side.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_BruhatTits_finite_quotEdge_of_finite_quotVert.lean

import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Mumford MulAction

theorem CerednikDrinfeld.BruhatTits.finite_quotEdge_of_finite_quotVert
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    {G : Type} [Group G] [MulAction G (LT.LatticeTree.Vertex R K₀)]
    [CerednikDrinfeld.Mumford.GraphAction G (CerednikDrinfeld.BruhatTits.tree R K₀)]
    [Finite (CerednikDrinfeld.Mumford.QuotVert G (LT.LatticeTree.Vertex R K₀))] :
    Finite (CerednikDrinfeld.Mumford.QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀)) := by sorry
