-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_inEdgeChart_of_edgeNondegAt_maximalIdeal
-- name    : CerednikDrinfeld.FormalOmega.DeligneDatum.inEdgeChart_of_edgeNondegAt_maximalIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/d710468d-8fde-59a9-84dd-f7b9d6513606
-- title:
--   Edge condition at the maximal ideal holds at every prime
-- statement:
--   Let $\mathcal O$ be a commutative ring, $K$ a field with an $\mathcal O$-algebra structure, $\pi$ an element of $\mathcal O$, and $B$ a local commutative $\mathcal O$-algebra. Let $d$ be a Deligne datum over $B$ for $\pi$, that is, an assignment to each full lattice $L$ in $K^2$ (a finitely generated $\mathcal O$-submodule of $K^2$ whose $K$-span is everything) of a $B$-submodule $d.\mathrm{line}\,L \subseteq B \otimes_{\mathcal O} L$ with invertible quotient, compatible with lattice inclusions and with homotheties $\mathrm{scalarGL}(c)$, and satisfying the nondegeneracy condition at every prime of $B$. Let $M'$ and $M$ be full lattices in $K^2$ and assume $d.\mathrm{EdgeNondegAt}$ holds at the maximal ideal $\mathfrak m$ of $B$ for the pair $(M',M)$, i.e. $M' \subseteq M$, $\pi v \in M'$ for every $v \in M$, every $v \in M \setminus M'$ satisfies $1 \otimes v \notin d.\mathrm{line}\,M + \mathfrak m\,(B \otimes_{\mathcal O} M)$, and every $v' \in M'$ not of the form $\pi w$ with $w \in M$ satisfies $1 \otimes v' \notin d.\mathrm{line}\,M' + \mathfrak m\,(B \otimes_{\mathcal O} M')$. Then $d.\mathrm{InEdgeChart}$ holds for $(M',M)$: the same four conditions hold with $\mathfrak m$ replaced by $\mathfrak p$, for every prime ideal $\mathfrak p$ of $B$.
--
--   This is the passage from Deligne's edge condition at the closed point of a local base to the condition at all primes, i.e. the statement that a $B$-point of the formal model lies in the edge chart attached to $(M',M)$ as soon as it does so modulo the maximal ideal. It is used in [`CerednikDrinfeld.FormalOmega.DeligneDatum.exists_isPullback_inEdgeChart_of_isLocalRing`](thm.html#CerednikDrinfeld.FormalOmega.DeligneDatum.exists_isPullback_inEdgeChart_of_isLocalRing), which produces, for a Deligne datum over a local ring, an edge chart containing the corresponding point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_inEdgeChart_of_edgeNondegAt_maximalIdeal.lean

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DeligneDatum.inEdgeChart_of_edgeNondegAt_maximalIdeal
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
    {B : Type} [CommRing B] [Algebra 𝒪 B] [IsLocalRing B]
    (d : DeligneDatum (K := K) π B) (M' M : FullLattice 𝒪 K)
    (h : d.EdgeNondegAt π (IsLocalRing.maximalIdeal B) M' M) :
    d.InEdgeChart π M' M := by sorry
