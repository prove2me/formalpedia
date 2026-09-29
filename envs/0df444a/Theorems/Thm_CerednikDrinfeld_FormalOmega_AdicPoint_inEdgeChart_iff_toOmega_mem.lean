-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem
-- name    : CerednikDrinfeld.FormalOmega.AdicPoint.inEdgeChart_iff_toOmega_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/ef50c7e5-953c-55c2-b315-48a9b048f256
-- title:
--   Edge chart membership via two vertex tubes and the edge tube
-- statement:
--   Fix a discrete valuation domain $\mathcal{O}$ with fraction field $K$, an element $\pi\in\mathcal{O}$, a field $C$ equipped with a $K$-algebra structure and a valuation with values in a linearly ordered commutative group with zero $\Gamma_0$, and a commutative $\mathcal{O}$-algebra $R$ mapping to $C$ compatibly with the $\mathcal{O}$- and $K$-structures. Let $\varpi$ be a pseudo-uniformizer of $K$ relative to $C$, that is an element $\varpi.\varpi\in K$ whose valuation in $C$ satisfies $0<v(\varpi.\varpi)<1$ and such that for every nonzero $a\in K$ there is $N$ with $v(\varpi.\varpi)^N\le v(a)\le v(\varpi.\varpi)^{-N}$. Assume `IsAdicFrame π ϖ R`: $\pi$ is irreducible, $R\to C$ is injective with image exactly the valuation ring $\{v\le 1\}$ of $C$, $R$ is $\pi$-adically complete, an element of $K$ has valuation $\le 1$ in $C$ precisely when it comes from $\mathcal{O}$, the image of $K$ in $C$ is closed, and $\pi$ and $\varpi.\varpi$ have the same image in $C$. Let $g\in \mathrm{GL}_2(K)$ and let $x$ be an adic point, i.e. a compatible system of Deligne data over the quotients `modPow π R n`. Writing $\sigma=$ `edgeFlip K ϖ` $=\mathrm{diag}(\varpi.\varpi,1)$, the assertion is an equivalence: the zeroth component $x.\mathrm{pt}\,0$ lies in the edge chart for the pair of full lattices $(g\sigma\cdot\mathcal{O}^2,\ g\cdot\mathcal{O}^2)$ — meaning that for every prime ideal of the base ring the datum satisfies the edge nondegeneracy condition `EdgeNondegAt` at that prime for this pair — if and only if the coordinate $x.\mathrm{toOmega}\,C\in C$ lies in the union of the vertex tube of the class of $g$ in $\mathrm{PGL}_2(K)$, the edge tube of that class, and the vertex tube of the class of $g\sigma$; here the vertex tube of $h$ consists of the points $z$ of the Drinfeld upper half plane with $\mathrm{pmoebius}(h^{-1})z$ in `affinoid ϖ 0`, and the edge tube of those with $\mathrm{pmoebius}(h^{-1})z$ in `stdEdgeTube ϖ`.
--
--   This is the chart-by-chart comparison between the formal (lattice-theoretic) description of the Drinfeld upper half plane and its analytic avatar: the $\mathcal{O}_C$-points reducing into the edge chart attached to the standard edge translated by $g$ are exactly those whose coordinate lies in the closed annulus cut out by the two rim vertex tubes together with the open annulus between them. It is used in the construction of finite coverings of the chart unit locus for the Čerednik–Drinfeld quotient, namely by [`CerednikDrinfeld.exists_finset_chartUnitLocus_cover_of_cerednikDrinfeld_quotient`](thm.html#CerednikDrinfeld.exists_finset_chartUnitLocus_cover_of_cerednikDrinfeld_quotient) and [`CerednikDrinfeld.exists_linearPieces_eq_chartUnitLocus_of_cerednikDrinfeld_quotient`](thm.html#CerednikDrinfeld.exists_linearPieces_eq_chartUnitLocus_of_cerednikDrinfeld_quotient).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFrame

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega

theorem CerednikDrinfeld.FormalOmega.AdicPoint.inEdgeChart_iff_toOmega_mem
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] {π : 𝒪}
    {C : Type} [Field C] [Algebra K C] [DecidableEq C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
    {R : Type} [CommRing R] [Algebra 𝒪 R] [Algebra R C] [Algebra 𝒪 C] [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K C]
    (ϖ : PseudoUniformizer K C) (hF : IsAdicFrame π ϖ R) (g : GL (Fin 2) K) (x : AdicPoint K π R) :
    (x.pt 0).InEdgeChart π (FullLattice.act (g * edgeFlip K ϖ) (stdFullLattice K)) (FullLattice.act g (stdFullLattice K)) ↔
      x.toOmega C ∈ Omega.vertexTube ϖ (Matrix.ProjGenLinGroup.mk g) ∪ Omega.edgeTube ϖ (Matrix.ProjGenLinGroup.mk g) ∪
        Omega.vertexTube ϖ (Matrix.ProjGenLinGroup.mk (g * edgeFlip K ϖ)) := by sorry
