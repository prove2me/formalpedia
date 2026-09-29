-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_inEdgeChart_swap
-- name    : CerednikDrinfeld.FormalOmega.DeligneDatum.inEdgeChart_swap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/41936f32-5411-5285-b2b5-04688205bd03
-- title:
--   Re-orienting an edge chart: from (M',M) to (π M,M')
-- statement:
--   Let $\mathcal O$ be a commutative ring, $K$ a field that is an $\mathcal O$-algebra, $\pi \in \mathcal O$, and $B$ a commutative $\mathcal O$-algebra. Let $c \in K^\times$ be a unit whose underlying element of $K$ is the image $\pi$ under $\mathcal O \to K$, and let $d$ be a Deligne datum for $\pi$ over $B$: an assignment, to each full lattice $M \subseteq K^2$ over $\mathcal O$, of a $B$-submodule $d.\mathrm{line}\,M \subseteq B \otimes_{\mathcal O} M$ with invertible quotient, compatible with inclusions of lattices, equivariant for the homothety isomorphisms, and nondegenerate at every prime of $B$. Let $M', M$ be full lattices such that $d$ lies in the edge chart of the ordered pair $(M', M)$, meaning that for every prime ideal $\mathfrak p \subseteq B$ one has $M' \subseteq M$, $\pi M \subseteq M'$, and: for every $v \in M$ with $v \notin M'$, $1 \otimes v \notin d.\mathrm{line}\,M + \mathfrak p\,(B \otimes_{\mathcal O} M)$, while for every $v' \in M'$ not of the form $\pi w$ with $w \in M$, $1 \otimes v' \notin d.\mathrm{line}\,M' + \mathfrak p\,(B \otimes_{\mathcal O} M')$. The conclusion is that $d$ lies in the edge chart of the pair $(cM, M')$, where $cM$ is the image of $M$ under the scalar matrix $c \cdot 1$, i.e. the same four conditions hold with small lattice $\pi M$ and big lattice $M'$.
--
--   The edge condition of Deligne's functorial description of the formal upper half plane attaches to an ordered pair $\pi M \subseteq M' \subseteq M$ of full lattices, that is, to an oriented edge of the Bruhat–Tits tree; this result says the condition is unchanged when the edge is read from its other vertex, the pair $(M', M)$ being replaced by $(\pi M, M')$. It is used in assembling finite covers of the formal scheme by edge charts and in the companion invariance statement under the inverse scalar action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_inEdgeChart_swap.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DeligneDatum.inEdgeChart_swap
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    (c : Kˣ) (hc : (c : K) = algebraMap 𝒪 K π)
    {d : DeligneDatum (K := K) π B} {M' M : FullLattice 𝒪 K} (hd : d.InEdgeChart π M' M) :
    d.InEdgeChart π (FullLattice.act (scalarGL c) M) M' := by sorry
