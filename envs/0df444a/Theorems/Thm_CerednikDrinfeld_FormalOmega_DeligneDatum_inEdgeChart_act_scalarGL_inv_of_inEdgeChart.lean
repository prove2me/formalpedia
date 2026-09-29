-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_inEdgeChart_act_scalarGL_inv_of_inEdgeChart
-- name    : CerednikDrinfeld.FormalOmega.DeligneDatum.inEdgeChart_act_scalarGL_inv_of_inEdgeChart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/80389df6-41a6-594b-acec-87fd8be77c98
-- title:
--   Reversing the orientation of an edge chart
-- statement:
--   Let $\mathcal{O}$ be a discrete valuation domain with fraction field $K$, let $\pi \in \mathcal{O}$ be irreducible, and let $c$ be a unit of $K$ whose image in $K$ equals the image of $\pi$ under the structure map $\mathcal{O} \to K$. Let $B$ be a commutative $\mathcal{O}$-algebra and let $d$ be a Deligne datum over $B$ for $\pi$, that is, an assignment to each full $\mathcal{O}$-lattice $M \subseteq K^2$ of a $B$-submodule $d.\mathrm{line}\,M$ of $B \otimes_{\mathcal{O}} M$ with invertible quotient, compatible with the maps induced by inclusions of lattices, equivariant for homotheties, and satisfying Deligne's non-degeneracy condition at every prime of $B$. Let $M'$ and $M$ be full lattices, and assume $d$ lies in the edge chart of the ordered pair $(M', M)$: for every prime ideal $\mathfrak{p}$ of $B$ one has $M' \subseteq M$, $\pi M \subseteq M'$, no $v \in M \setminus M'$ has $1 \otimes v \in d.\mathrm{line}\,M + \mathfrak{p}\,(B \otimes_{\mathcal{O}} M)$, and no $v' \in M' \setminus \pi M$ has $1 \otimes v' \in d.\mathrm{line}\,M' + \mathfrak{p}\,(B \otimes_{\mathcal{O}} M')$. Then $d$ lies in the edge chart of the pair $(M, c^{-1}M')$, where $c^{-1}M'$ is the image of $M'$ under the scalar matrix $c^{-1} \cdot 1 \in \mathrm{GL}_2(K)$.
--
--   The edge charts of the formal model of the $p$-adic upper half plane are indexed by oriented edges of the Bruhat–Tits tree; this statement says that the chart condition is insensitive to the choice of orientation, the pair $(M', M)$ with $\pi M \subseteq M' \subseteq M$ being replaced by $(M, \pi^{-1}M')$. It is used when an edge must be presented with a prescribed one of its two vertices as the smaller lattice, in the construction of the quadruple attached to a Deligne datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_inEdgeChart_act_scalarGL_inv_of_inEdgeChart.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DeligneDatum.inEdgeChart_act_scalarGL_inv_of_inEdgeChart
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (π : 𝒪) (hπ : Irreducible π) (c : Kˣ) (hc : (c : K) = algebraMap 𝒪 K π)
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    (d : DeligneDatum (K := K) π B) (M' M : FullLattice 𝒪 K) (hd : d.InEdgeChart π M' M) :
    d.InEdgeChart π M (FullLattice.act (scalarGL c⁻¹) M') := by sorry
