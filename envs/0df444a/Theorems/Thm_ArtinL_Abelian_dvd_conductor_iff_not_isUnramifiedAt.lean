-- Prove2me | Theorems.Thm_ArtinL_Abelian_dvd_conductor_iff_not_isUnramifiedAt
-- name    : ArtinL.Abelian.dvd_conductor_iff_not_isUnramifiedAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/4831a582-b57e-5626-9476-a3c253b1f82b
-- title:
--   Primes dividing the Artin conductor are exactly the ramified ones
-- statement:
--   Let $K$ and $M$ be number fields with $M$ a Galois extension of $K$ (an algebra structure of $K$ on $M$ together with `IsGalois K M`), let $\psi\colon \mathrm{Gal}(M/K)=(M\simeq_{\mathrm{alg}[K]}M)\to\mathbb{C}^{\times}$ be a group homomorphism into the units of $\mathbb{C}$, and let $v$ be a point of the height-one spectrum of the ring of integers $\mathcal{O}_K$, i.e. a nonzero prime ideal $v.\mathrm{asIdeal}$ of $\mathcal{O}_K$. The assertion is an equivalence: $v.\mathrm{asIdeal}$ divides the ideal [`ArtinL.Abelian.conductor`](def/ArtinL_Abelian.html#L57) $\psi$, defined as the multiplicative finite-support product $\prod_{w}w.\mathrm{asIdeal}^{\,e(\psi,w)}$ over all height-one primes $w$ of $\mathcal{O}_K$ with exponent $e(\psi,w)$ equal to $1$ if $\psi$ is ramified at $w$ and $0$ otherwise, plus $\lceil \mathrm{swanConductor}\,\psi\,w\rceil$, if and only if $\psi$ fails to satisfy [`ArtinL.Abelian.IsUnramifiedAt`](def/ArtinL_Abelian.html#L33) at $v$, that is, if and only if there is some $\sigma$ in the inertia subgroup of $\mathrm{Gal}(M/K)$ attached to the chosen prime of $\mathcal{O}_M$ above $v$ with $\psi(\sigma)\neq 1$.
--
--   This identifies the support of the Artin conductor of a one-dimensional character of $\mathrm{Gal}(M/K)$ with its set of ramified primes, the divisibility criterion being the form in which the conductor is used downstream; it is invoked in the construction of ray class characters with prescribed conductor and in the production of a Galois element on which such a character is non-trivial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ArtinL_Abelian_dvd_conductor_iff_not_isUnramifiedAt.lean

import Mathlib
import Definitions.Def_ArtinL_Abelian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

universe u v

theorem ArtinL.Abelian.dvd_conductor_iff_not_isUnramifiedAt
    (K : Type u) (M : Type v) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsGalois K M] (ψ : (M ≃ₐ[K] M) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) :
    v.asIdeal ∣ ArtinL.Abelian.conductor ψ ↔ ¬ ArtinL.Abelian.IsUnramifiedAt ψ v := by sorry
