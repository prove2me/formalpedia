-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_isOpen_setOf_edgeNondegAt
-- name    : CerednikDrinfeld.FormalOmega.DeligneDatum.isOpen_setOf_edgeNondegAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/cb9a6166-2154-573a-89d9-7854f6a77ad1
-- title:
--   Openness of the edge nondegeneracy locus in Spec B
-- statement:
--   Let $\mathcal O$ be a commutative ring, $K$ a field which is an $\mathcal O$-algebra, and $\pi \in \mathcal O$ an element such that the quotient $\mathcal O/(\pi)$ is finite; let $B$ be a commutative $\mathcal O$-algebra in which the image of $\pi$ is nilpotent. Let $d$ be a Deligne datum for $(\pi, B)$, that is, an assignment to each full lattice $M \subset K^2$ (a finitely generated $\mathcal O$-submodule spanning $K^2$ over $K$) of a $B$-submodule $d.\mathrm{line}\,M \subseteq B \otimes_{\mathcal O} M$ with invertible quotient, compatible with lattice inclusions and with the action of scalar homotheties $\mathrm{scalarGL}(c)$, $c \in K^\times$, and satisfying at every prime ideal of $B$ the nondegeneracy condition for some pair of lattices. Let $M', M$ be full lattices in $K^2$. Then the set of primes $\mathfrak p \in \operatorname{Spec} B$ at which `d.EdgeNondegAt` holds for the pair $(M', M)$ — namely $M' \subseteq M$, $\pi M \subseteq M'$, every $v \in M \setminus M'$ has $1 \otimes v \notin d.\mathrm{line}\,M + \mathfrak p\,(B \otimes_{\mathcal O} M)$, and every $v' \in M'$ not of the form $\pi w$ with $w \in M$ has $1 \otimes v' \notin d.\mathrm{line}\,M' + \mathfrak p\,(B \otimes_{\mathcal O} M')$ — is open in $\operatorname{Spec} B$.
--
--   This is the openness, in the Zariski topology on $\operatorname{Spec} B$, of the locus where a Deligne datum satisfies the edge condition at a fixed edge $(M', M)$ of the Bruhat–Tits tree; the first two clauses are conditions on the lattices alone, while the remaining two are non-vanishing conditions on the invertible quotients. It is used in the construction of the formal scheme $\hat\Omega$, both to cover the functor of nilpotent points by open subfunctors cut out by edge conditions and in the representability statement over Noetherian base rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_isOpen_setOf_edgeNondegAt.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DeligneDatum.isOpen_setOf_edgeNondegAt
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪) [Finite (𝒪 ⧸ Ideal.span {π})]
    {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (d : DeligneDatum (K := K) π B) (M' M : FullLattice 𝒪 K) :
    IsOpen {𝔭 : PrimeSpectrum B | d.EdgeNondegAt π 𝔭.asIdeal M' M} := by sorry
