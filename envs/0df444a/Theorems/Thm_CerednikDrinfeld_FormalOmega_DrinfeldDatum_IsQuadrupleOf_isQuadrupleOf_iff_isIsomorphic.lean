-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_isQuadrupleOf_iff_isIsomorphic
-- name    : CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.isQuadrupleOf_iff_isIsomorphic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/64c5d271-751c-51a2-8028-136b3bbd2475
-- title:
--   Drinfeld quadruples over a Deligne datum are unique up to isomorphism
-- statement:
--   Let $\mathcal O$ be a discrete valuation ring that is a domain, $K$ a field which is an $\mathcal O$-algebra and the fraction field of $\mathcal O$, and $\pi \in \mathcal O$ irreducible. Let $B$ be a commutative $\mathcal O$-algebra in which the image of $\pi$ is nilpotent. Let $Q$ be a Drinfeld datum over $B$ for $\pi$ — that is, two assignments $x \mapsto N_0(x), N_1(x)$ of full $\mathcal O$-lattices in $K^2$ to points of $\operatorname{Spec} B$ with $N_0(x) \le N_1(x)$ and $\pi N_1(x) \subseteq N_0(x)$, locally constant in the sense that each set $\{x : v \in N_i(x)\}$ is open, together with invertible $B$-modules $T_0, T_1$, $B$-linear maps $\Pi_0 : T_0 \to T_1$ and $\Pi_1 : T_1 \to T_0$ whose two composites are multiplication by $\pi$, and stalkwise maps $u_i(x)$ from the base change of $N_i(x)$ to the localisation $B_x$ into the stalk of $T_i$ at $x$, compatible with the inclusions, with $\Pi_0$ and with multiplication by $\pi$. Let $d$ be a Deligne datum over $B$: a family of $B$-submodules $\mathrm{line}(M) \subseteq B \otimes_{\mathcal O} M$, one for each full lattice $M$, with invertible quotient, monotone under inclusions of lattices, equivariant for scalar homotheties, and satisfying the nondegeneracy condition at every prime of $B$. Assume $Q$ is a quadruple of $d$, i.e. for every $x \in \operatorname{Spec} B$ the pair of full lattices $Q.L_0(x), Q.L_1(x)$ attached to $x$ satisfies the edge-nondegeneracy condition for $d$ at the prime of $x$, and the kernels of $u_0(x)$ and $u_1(x)$ are exactly the lines that the Deligne datum obtained from $d$ by base change along $B \to B_x$ attaches to $Q.L_0(x)$ and $Q.L_1(x)$. Then for every Drinfeld datum $Q'$ over $B$ for $\pi$, $Q'$ is a quadruple of $d$ if and only if $Q'$ is isomorphic to $Q$, i.e. an isomorphism of Drinfeld data from $Q'$ to $Q$ exists.
--
--   This is the uniqueness-up-to-isomorphism half of the equivalence between Drinfeld quadruples and Deligne data over a base in which $\pi$ is nilpotent, as in Boutot–Carayol's account of the Čerednik–Drinfeld uniformisation. It is used in the existence-and-uniqueness statements for quadruples attached to a Deligne datum, in particular in assembling a quadruple from local ones and in the comparison of charts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_isQuadrupleOf_iff_isIsomorphic.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.isQuadrupleOf_iff_isIsomorphic
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π)
    {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    {Q : DrinfeldDatum (K := K) π B} {d : DeligneDatum (K := K) π B} (h : Q.IsQuadrupleOf d)
    (Q' : DrinfeldDatum (K := K) π B) : Q'.IsQuadrupleOf d ↔ Q'.IsIsomorphic Q := by sorry
