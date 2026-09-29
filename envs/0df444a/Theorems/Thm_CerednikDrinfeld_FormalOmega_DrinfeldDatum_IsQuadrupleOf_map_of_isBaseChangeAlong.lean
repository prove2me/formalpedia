-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_map_of_isBaseChangeAlong
-- name    : CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.map_of_isBaseChangeAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/b991433f-8202-53b9-81b2-46b3de744347
-- title:
--   Naturality in the test algebra of the quadruple–point comparison
-- statement:
--   Let $\mathcal{O}$ be a commutative ring, $K$ a field with an $\mathcal{O}$-algebra structure, $\pi \in \mathcal{O}$, and let $f : B \to B'$ be a homomorphism of commutative $\mathcal{O}$-algebras. Let $Q$ be a `DrinfeldDatum` for $(\pi, K)$ over $B$ and $Q'$ one over $B'$, and let $d$ be a `DeligneDatum` for $(\pi, K)$ over $B$, that is, an assignment $M \mapsto d.\mathrm{line}\,M$ of a $B$-submodule of $B \otimes_{\mathcal{O}} M$ to each full $\mathcal{O}$-lattice $M \subset K^2$, with invertible quotients, monotone under inclusions of lattices, equivariant for scalar homotheties, and satisfying the nondegeneracy condition at every prime of $B$. Assume $Q$ is a quadruple of $d$: for every $x \in \operatorname{Spec} B$ the predicate `EdgeNondegAt` holds for $d$, the ideal of $x$ and the full lattices $Q.L_0\,x$, $Q.L_1\,x$, and the kernels of the stalk comparison maps $Q.u_0\,x$, $Q.u_1\,x$ coincide with the lines of the base change $d.\mathrm{map}\,\pi$ along $B \to B_x$ at $Q.L_0\,x$ and $Q.L_1\,x$. Assume further that $Q'$ is a base change of $Q$ along $f$, i.e. there exists a `BaseChangeAlong` datum: the lattices of $Q'$ at $x'$ are those of $Q$ at the point of $\operatorname{Spec} B$ under $x'$, together with $f$-semilinear maps $\tau_0, \tau_1$ on the invertible modules whose images span over $B'$, commuting with $\Pi_0$ and $\Pi_1$, and transforming the stalk maps $u_0, u_1$ in the prescribed way. Then $Q'$ is a quadruple of the base-changed Deligne datum $d.\mathrm{map}\,\pi\,f$.
--
--   This is the naturality in the test algebra of the comparison between Drinfeld's functor of quadruples and the functor of points of the formal upper half plane: the property of being the quadruple attached to a point of $\widehat{\Omega}$ is stable under base change of the test algebra. It is used in the construction of a Drinfeld datum from local data over a cover, in the associated covering statement, and in the comparison with Cartier quadruples on special formal schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_map_of_isBaseChangeAlong.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.map_of_isBaseChangeAlong
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B')
    {Q : DrinfeldDatum (K := K) π B} {Q' : DrinfeldDatum (K := K) π B'} {d : DeligneDatum (K := K) π B}
    (h : Q.IsQuadrupleOf d) (hf : Q.IsBaseChangeAlong f Q') : Q'.IsQuadrupleOf (d.map π f) := by sorry
