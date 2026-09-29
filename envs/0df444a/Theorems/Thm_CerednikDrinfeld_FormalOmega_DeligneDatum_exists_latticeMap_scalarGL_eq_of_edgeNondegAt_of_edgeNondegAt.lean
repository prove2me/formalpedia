-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_latticeMap_scalarGL_eq_of_edgeNondegAt_of_edgeNondegAt
-- name    : CerednikDrinfeld.FormalOmega.DeligneDatum.exists_latticeMap_scalarGL_eq_of_edgeNondegAt_of_edgeNondegAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/99743826-fc6f-5709-aa11-7d1cc21f35d9
-- title:
--   Two edge-nondegenerate lattice pairs of a Deligne datum share a vertex
-- statement:
--   Let $\mathcal O$ be a discrete valuation domain with field of fractions $K$, let $\pi \in \mathcal O$ be irreducible, and let $B$ be a commutative $\mathcal O$-algebra. Let $d$ be a Deligne datum for $\pi$ over $B$, that is, an assignment to every full lattice $M \subset K^2$ (a finitely generated $\mathcal O$-submodule of $K^2$ spanning $K^2$ over $K$) of a $B$-submodule $d.\mathrm{line}\,M$ of $B \otimes_{\mathcal O} M$ with invertible quotient, compatible with inclusions of lattices and with the homotheties $c \cdot \mathrm{id}$ for $c \in K^\times$, and nondegenerate at every prime of $B$. Let $\mathfrak p$ be a prime ideal of $B$ containing the image of $\pi$, and let $M', M, L', L$ be full lattices such that both pairs $(M', M)$ and $(L', L)$ satisfy the edge nondegeneracy condition at $\mathfrak p$: $M' \subseteq M$, $\pi M \subseteq M'$, for every $v \in M$ with $v \notin M'$ the element $1 \otimes v$ lies outside $d.\mathrm{line}\,M + \mathfrak p \cdot (B \otimes_{\mathcal O} M)$, and for every $v' \in M'$ not of the form $\pi w$ with $w \in M$ the element $1 \otimes v'$ lies outside $d.\mathrm{line}\,M' + \mathfrak p \cdot (B \otimes_{\mathcal O} M')$, and likewise for $(L', L)$. Then there are $c \in K^\times$ and full lattices $X, Y$ with $X \in \{M', M\}$, $Y \in \{L', L\}$ and $c \cdot X = Y$, the left-hand side being the image of $X$ under the scalar matrix $c \cdot 1$.
--
--   This is the statement that two edges of the Bruhat–Tits tree of $\mathrm{GL}_2(K)$ whose lattice pairs both satisfy Deligne's edge condition for a given point of the formal upper half plane at a prime containing $\pi$ necessarily share a vertex up to homothety, the combinatorial input behind the fact that the formal opens attached to distinct simplices meet only along common faces. It is used in the analysis of Drinfeld data, in particular in the identification of the quadruple of lattices attached to such a point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_latticeMap_scalarGL_eq_of_edgeNondegAt_of_edgeNondegAt.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DeligneDatum.exists_latticeMap_scalarGL_eq_of_edgeNondegAt_of_edgeNondegAt
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π)
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B) [𝔭.IsPrime] (h𝔭 : algebraMap 𝒪 B π ∈ 𝔭)
    (M' M L' L : FullLattice 𝒪 K) (hM : d.EdgeNondegAt π 𝔭 M' M) (hL : d.EdgeNondegAt π 𝔭 L' L) :
    ∃ (c : Kˣ) (X Y : FullLattice 𝒪 K), (X = M' ∨ X = M) ∧ (Y = L' ∨ Y = L) ∧
      latticeMap (scalarGL c) X.1 = Y.1 := by sorry
