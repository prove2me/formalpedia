-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_pullback_of_isTranslateOdd
-- name    : CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.pullback_of_isTranslateOdd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/cabbd071-7723-5275-83d7-36355b99c1bf
-- title:
--   Odd translates preserve the quadruple–Deligne datum correspondence
-- statement:
--   Let $\mathcal{O}$ be a commutative ring, $K$ a field which is an $\mathcal{O}$-algebra, $\pi \in \mathcal{O}$, and $B$ a commutative $\mathcal{O}$-algebra. Let $g \in \mathrm{GL}_2(K)$, let $c_0, c_1 \in K^\times$, let $Q, Q'$ be Drinfeld data over $B$ for $\pi$, and let $d$ be a Deligne datum over $B$ for $\pi$ (a choice of $B$-submodule $d.\text{line}(M) \subseteq B \otimes_{\mathcal{O}} M$ for every full $\mathcal{O}$-lattice $M \subseteq K^2$, with invertible quotients, monotone, homothety-equivariant and satisfying the nondegeneracy clause at each prime of $B$). Assume first that $Q$ is a quadruple of $d$, i.e. `IsQuadrupleOf` holds: for every prime $x$ of $B$ the predicate `EdgeNondegAt` holds for $d$ at $x.\mathrm{asIdeal}$ and the pair of lattices $Q.L_0 x$, $Q.L_1 x$, and the kernels of the stalk maps $Q.u_0 x$, $Q.u_1 x$ are the lines cut out at $Q.L_0 x$, $Q.L_1 x$ by the base change of $d$ along $B \to$ `locRing B x`. Assume second `IsTranslateOdd`, i.e. there is a `TranslateOdd` structure for $(g, c_0, c_1)$ from $Q$ to $Q'$: $c_0 = \pi c_1$ in $K$; for all primes $x$, $Q'.N_0 x = (c_0 g^{-1}) Q.N_1 x$ and $Q'.N_1 x = (c_1 g^{-1}) Q.N_0 x$ as images under `latticeMap`; there are $B$-linear isomorphisms $\sigma_0 : Q.T_1 \to Q'.T_0$ and $\sigma_1 : Q.T_0 \to Q'.T_1$ with $\sigma_1 \circ Q.\Pi_1 = Q'.\Pi_0 \circ \sigma_0$ and $\sigma_0 \circ Q.\Pi_0 = Q'.\Pi_1 \circ \sigma_1$, compatible with the stalk maps in the sense that $Q'.u_0 x (1 \otimes (c_0 g^{-1}) w) = \sigma_0(Q.u_1 x(1 \otimes w))$ for $w \in Q.N_1 x$ and $Q'.u_1 x(1 \otimes (c_1 g^{-1}) v) = \sigma_1(Q.u_0 x(1 \otimes v))$ for $v \in Q.N_0 x$. Then $Q'$ is a quadruple of `DeligneDatum.pullback π B g d`, the Deligne datum whose line at $M$ is the preimage of $d.\text{line}(gM)$ under the isomorphism `actBaseChange B g M`.
--
--   This is the half of the $\mathrm{GL}_2(K)$-equivariance of Drinfeld's identification of the functor of quadruples with the formal upper half plane in which the determinant of $g$ has odd valuation, so that the two graded pieces of the quadruple are interchanged. It is used in the descent of the comparison along base changes and in the construction of pullbacks of period values attached to translates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_pullback_of_isTranslateOdd.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.pullback_of_isTranslateOdd
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B] (g : GL (Fin 2) K) (c₀ c₁ : Kˣ)
    {Q Q' : DrinfeldDatum (K := K) π B} {d : DeligneDatum (K := K) π B}
    (h : Q.IsQuadrupleOf d) (ht : Q.IsTranslateOdd g c₀ c₁ Q') :
    Q'.IsQuadrupleOf (DeligneDatum.pullback π B g d) := by sorry
