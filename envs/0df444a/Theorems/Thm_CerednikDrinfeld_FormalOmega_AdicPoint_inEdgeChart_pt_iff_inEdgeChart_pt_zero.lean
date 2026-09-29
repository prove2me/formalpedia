-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_pt_iff_inEdgeChart_pt_zero
-- name    : CerednikDrinfeld.FormalOmega.AdicPoint.inEdgeChart_pt_iff_inEdgeChart_pt_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/4d09ebc4-4598-52d6-9774-74e92c3fc92d
-- title:
--   Edge-chart membership of an adic point is level-independent
-- statement:
--   Let $\mathcal{O}$ be a discrete valuation ring (a commutative domain with the discrete valuation ring property), let $K$ be a field equipped with an $\mathcal{O}$-algebra structure making it the fraction field of $\mathcal{O}$, let $\pi \in \mathcal{O}$, and let $R$ be a commutative $\mathcal{O}$-algebra. Let $x$ be an adic point of the formal upper half plane over $R$, that is, a family $x_m$ of Deligne data for $\pi$ over the rings $R/(\pi^{m+1})$, one for each $m \in \mathbb{N}$, compatible in the sense that the functorial image of $x_{m+1}$ under the transition map $R/(\pi^{m+2}) \to R/(\pi^{m+1})$ is $x_m$. Let $n \in \mathbb{N}$ and let $M', M$ be full lattices in $K^2$ over $\mathcal{O}$, i.e. finitely generated $\mathcal{O}$-submodules of $K^2$ whose $K$-span is all of $K^2$. Then $x_n$ satisfies the edge-chart condition for the pair $(M', M)$ if and only if $x_0$ does. Here a Deligne datum $d$ over a ring $B$ satisfies that condition when for every prime ideal $\mathfrak{p}$ of $B$ one has $M' \le M$, $\pi v \in M'$ for all $v \in M$, every $v \in M$ with $v \notin M'$ has $1 \otimes v \notin d.\mathrm{line}(M) + \mathfrak{p}\cdot(B \otimes_{\mathcal{O}} M)$, and every $v' \in M'$ not of the form $\pi w$ with $w \in M$ has $1 \otimes v' \notin d.\mathrm{line}(M') + \mathfrak{p}\cdot(B \otimes_{\mathcal{O}} M')$; for $x_n$ the ring $B$ is $R/(\pi^{n+1})$ and for $x_0$ it is $R/(\pi)$.
--
--   The formal upper half plane $\widehat{\Omega}$ is covered by charts attached to the vertices and the edges of the Bruhat–Tits tree of $\mathrm{PGL}_2(K)$, an edge chart being cut out by Deligne's nondegeneracy condition at a pair of adjacent lattice classes; this statement says that for an adic point, lying in a given edge chart can be tested at the first level $R/(\pi)$, with no hypothesis on $R$ beyond being an $\mathcal{O}$-algebra. It is used in the analysis of the Čerednik–Drinfeld quotient, namely by [`CerednikDrinfeld.exists_finset_chartUnitLocus_cover_of_cerednikDrinfeld_quotient`](thm.html#CerednikDrinfeld.exists_finset_chartUnitLocus_cover_of_cerednikDrinfeld_quotient) and [`CerednikDrinfeld.exists_linearPieces_eq_chartUnitLocus_of_cerednikDrinfeld_quotient`](thm.html#CerednikDrinfeld.exists_linearPieces_eq_chartUnitLocus_of_cerednikDrinfeld_quotient).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_pt_iff_inEdgeChart_pt_zero.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFrame

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega

theorem CerednikDrinfeld.FormalOmega.AdicPoint.inEdgeChart_pt_iff_inEdgeChart_pt_zero
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] {π : 𝒪}
    {R : Type} [CommRing R] [Algebra 𝒪 R] (x : AdicPoint K π R) (n : ℕ) (M' M : FullLattice 𝒪 K) :
    (x.pt n).InEdgeChart π M' M ↔ (x.pt 0).InEdgeChart π M' M := by sorry
