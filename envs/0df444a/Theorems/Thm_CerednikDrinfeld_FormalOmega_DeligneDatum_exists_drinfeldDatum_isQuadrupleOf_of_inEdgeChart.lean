-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_drinfeldDatum_isQuadrupleOf_of_inEdgeChart
-- name    : CerednikDrinfeld.FormalOmega.DeligneDatum.exists_drinfeldDatum_isQuadrupleOf_of_inEdgeChart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/09d95760-3d24-58f3-983b-5553ef7ca9d6
-- title:
--   Drinfeld quadruple for a Deligne datum in an edge chart
-- statement:
--   Let $\mathcal O$ be a discrete valuation ring with fraction field $K$, let $\pi\in\mathcal O$ be irreducible, and let $B$ be a commutative $\mathcal O$-algebra in which the image of $\pi$ is nilpotent. Let $M'\subseteq M$ be full $\mathcal O$-lattices in $K^2$ with $\pi M\subseteq M'$, and assume $M'$ has determinant index $0$, i.e. $M'=g\cdot(\mathcal O^2)$ for some $g\in \mathrm{GL}_2(K)$ whose determinant is the image of a unit of $\mathcal O$. Let $d$ be a Deligne datum over $B$: an assignment of a $B$-submodule $d.\mathrm{line}\,N\subseteq B\otimes_{\mathcal O}N$ to each full lattice $N$, with invertible quotient, monotone under inclusions of lattices, equivariant for homotheties, and nondegenerate at each prime of $B$ along some edge. Assume $d$ lies in the edge chart of $(M',M)$: for every prime $\mathfrak p\subseteq B$, every $v\in M\setminus M'$ has $1\otimes v\notin d.\mathrm{line}\,M+\mathfrak p\,(B\otimes M)$, and every $v'\in M'$ not of the form $\pi w$ with $w\in M$ has $1\otimes v'\notin d.\mathrm{line}\,M'+\mathfrak p\,(B\otimes M')$. Then there exists a Drinfeld datum $Q$ over $B$ — two lattice functions $N_0\le N_1$ on $\operatorname{Spec}B$ with $\pi N_1\subseteq N_0$ and open membership loci, invertible $B$-modules $T_0,T_1$ with maps $\Pi_0,\Pi_1$ composing to multiplication by $\pi$ both ways, localised comparison maps $u_0,u_1$ from the base-changed lattices to the stalks, and the further compatibilities of the structure — which is a quadruple for $d$: at each prime $x$ of $B$ the datum $d$ is edge-nondegenerate along $(Q.L_0\,x,Q.L_1\,x)$, and the kernels of $u_0\,x$ and $u_1\,x$ are the lines of the base change of $d$ along $B\to B_x$ at $Q.L_0\,x$ and $Q.L_1\,x$.
--
--   This is the local half of the comparison between Deligne data on the formal upper half-plane and Drinfeld quadruples (Boutot–Carayol I §5): when the datum is constrained to a single edge chart, the quadruple can be written down directly from the two lattices of the edge, with no gluing over $\operatorname{Spec}B$. It is the input to [`CerednikDrinfeld.FormalOmega.DeligneDatum.exists_drinfeldDatum_isQuadrupleOf`](thm.html#CerednikDrinfeld.FormalOmega.DeligneDatum.exists_drinfeldDatum_isQuadrupleOf), which removes the edge-chart hypothesis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_drinfeldDatum_isQuadrupleOf_of_inEdgeChart.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DeligneDatum.exists_drinfeldDatum_isQuadrupleOf_of_inEdgeChart
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π)
    {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    {M' M : FullLattice 𝒪 K} (hle : M'.1 ≤ M.1) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (h0 : HasDetIndex π M'.1 0)
    (d : DeligneDatum (K := K) π B) (hd : d.InEdgeChart π M' M) :
    ∃ Q : DrinfeldDatum (K := K) π B, Q.IsQuadrupleOf d := by sorry
