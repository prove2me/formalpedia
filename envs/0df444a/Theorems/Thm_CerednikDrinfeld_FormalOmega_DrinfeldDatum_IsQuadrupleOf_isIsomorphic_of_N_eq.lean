-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_isIsomorphic_of_N_eq
-- name    : CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.isIsomorphic_of_N_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/a5fb33dc-ee8a-5282-a7c5-7694bea883db
-- title:
--   Uniqueness of a Drinfeld datum over a Deligne datum
-- statement:
--   Let $\mathcal O$ be a discrete valuation ring which is a domain, $K$ a field that is the fraction field of $\mathcal O$, and $\pi \in \mathcal O$ an irreducible element. Let $B$ be an $\mathcal O$-algebra in which the image of $\pi$ is nilpotent. Let $d$ be a Deligne datum for $\pi$ over $B$, and let $Q$ and $Q'$ be Drinfeld data for $\pi$ over $B$: each consists of two functions $N_0, N_1$ from $\mathrm{Spec}\,B$ to the full $\mathcal O$-lattices in $K^2$ with $N_0(x) \le N_1(x)$ and $\pi N_1(x) \subseteq N_0(x)$, the membership loci $\{x : v \in N_i(x)\}$ being open, together with invertible $B$-modules $T_0, T_1$, maps $\Pi_0 : T_0 \to T_1$ and $\Pi_1 : T_1 \to T_0$ whose two composites are multiplication by $\pi$, and, at each prime $x$, comparison maps $u_i(x)$ from $B_x \otimes_{\mathcal O} N_i(x)$ to the stalk of $T_i$ at $x$, compatible with the inclusion $N_0(x) \le N_1(x)$, with $\Pi_0$ and with multiplication by $\pi$. Assume that $Q$ and $Q'$ are both quadruples of $d$, that is, for every prime $x$ the pair $(N_0(x), N_1(x))$ is edge-nondegenerate for $d$ at $x$ and the kernels of $u_0(x)$ and $u_1(x)$ are the lines that the base change of $d$ along $B \to B_x$ assigns to $N_0(x)$ and $N_1(x)$. Assume finally that the lattice functions agree: $Q.N_0(x) = Q'.N_0(x)$ and $Q.N_1(x) = Q'.N_1(x)$ for all primes $x$ of $B$. Then the type `Iso Q' Q` of isomorphisms of Drinfeld data from $Q'$ to $Q$ is nonempty, i.e. $Q'$ and $Q$ are isomorphic.
--
--   This is the rigidity half of the comparison between Drinfeld quadruples and Deligne data in the Čerednik–Drinfeld uniformisation: a Drinfeld quadruple is determined up to isomorphism by its associated Deligne datum together with its pair of lattice functions. It is used in the proof that being a quadruple of a common Deligne datum is equivalent to being isomorphic, [`CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.isQuadrupleOf_iff_isIsomorphic`](thm.html#CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.isQuadrupleOf_iff_isIsomorphic), and the argument proceeds by gluing the stalkwise isomorphisms supplied by the agreeing kernels, via [`LinearMap.exists_forall_localizedModule_mk_eq_of_forall_exists_chart`](thm.html#LinearMap.exists_forall_localizedModule_mk_eq_of_forall_exists_chart).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_isIsomorphic_of_N_eq.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.isIsomorphic_of_N_eq
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π)
    {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    {Q : DrinfeldDatum (K := K) π B} {d : DeligneDatum (K := K) π B} (h : Q.IsQuadrupleOf d)
    (Q' : DrinfeldDatum (K := K) π B) (h' : Q'.IsQuadrupleOf d)
    (h₀ : ∀ x : PrimeSpectrum B, Q.N₀ x = Q'.N₀ x) (h₁ : ∀ x : PrimeSpectrum B, Q.N₁ x = Q'.N₁ x) :
    Q'.IsIsomorphic Q := by sorry
