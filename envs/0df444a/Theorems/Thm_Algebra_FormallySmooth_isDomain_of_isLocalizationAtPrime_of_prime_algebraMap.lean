-- Prove2me | Theorems.Thm_Algebra_FormallySmooth_isDomain_of_isLocalizationAtPrime_of_prime_algebraMap
-- name    : Algebra.FormallySmooth.isDomain_of_isLocalizationAtPrime_of_prime_algebraMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/6d292b08-45b4-5b39-a2ac-d38994872d28
-- title:
--   Local rings of smooth DVR-algebras with prime uniformiser are domains
-- statement:
--   Let $A$ be a discrete valuation ring (a commutative domain that is a discrete valuation ring in Mathlib's sense), and let $B$ be a commutative $A$-algebra that is both formally smooth and of finite presentation over $A$. Let $\varpi \in A$ be an element generating the maximal ideal of the local ring $A$, i.e. $\mathrm{maximalIdeal}\,A = (\varpi)$, and assume that the image $\varphi(\varpi)$ of $\varpi$ under the structure map $\varphi \colon A \to B$ is a prime element of $B$. Let $\mathfrak n \subset B$ be a maximal ideal with $\varphi(\varpi) \in \mathfrak n$, and let $S$ be a commutative $B$-algebra which is a localisation of $B$ at the prime $\mathfrak n$, i.e. at the multiplicative set $B \setminus \mathfrak n$, and which is local. The conclusion is that $S$ is an integral domain: it is nontrivial and has no zero divisors.
--
--   This is the standard fact that a smooth algebra over a discrete valuation ring whose special fibre is integral along a given closed point has integral local ring there, in the form needed for the construction of étale coordinates. It supplies the `IsDomain` hypothesis used in [`Algebra.FormallySmooth.exists_etaleCoordinate_of_krullDimLE_one`](thm.html#Algebra.FormallySmooth.exists_etaleCoordinate_of_krullDimLE_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_FormallySmooth_isDomain_of_isLocalizationAtPrime_of_prime_algebraMap.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem Algebra.FormallySmooth.isDomain_of_isLocalizationAtPrime_of_prime_algebraMap
    {A B S : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [Algebra A B]
    [Algebra.FormallySmooth A B] [Algebra.FinitePresentation A B]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ})
    (hprime : Prime (algebraMap A B ϖ))
    (𝔫 : Ideal B) [𝔫.IsMaximal] (hϖ𝔫 : algebraMap A B ϖ ∈ 𝔫)
    [CommRing S] [Algebra B S] [IsLocalization.AtPrime S 𝔫] [IsLocalRing S] :
    IsDomain S := by sorry
