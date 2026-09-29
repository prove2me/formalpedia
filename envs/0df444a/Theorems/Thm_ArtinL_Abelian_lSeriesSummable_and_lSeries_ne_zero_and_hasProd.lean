-- Prove2me | Theorems.Thm_ArtinL_Abelian_lSeriesSummable_and_lSeries_ne_zero_and_hasProd
-- name    : ArtinL.Abelian.lSeriesSummable_and_lSeries_ne_zero_and_hasProd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/6c360663-4291-5a3e-8fbb-eca2e537acc8
-- title:
--   Euler product and non-vanishing of abelian Artin L-series
-- statement:
--   Let $K$ and $M$ be number fields with $M$ an algebra over $K$ which is Galois over $K$, let $\psi$ be a monoid homomorphism from the Galois group $M \simeq_{\mathrm{alg}[K]} M$ to $\mathbb{C}^{\times}$, and let $s \in \mathbb{C}$ with $\operatorname{Re} s > 1$. For a non-zero prime $v$ of $\mathcal{O}_K$ (a point of the height-one spectrum) set [`ArtinL.Abelian.localValue`](def/ArtinL_Abelian.html#L36) $\psi\,v$ to be the complex number $\psi(\sigma_v)$, where $\sigma_v$ is the arithmetic Frobenius [`LanglandsTunnell.P2.Artin.artinFrob`](def/LanglandsTunnell_ArtinFrobenius.html#L72) attached to a prime of $M$ above $v$, in case $\psi$ is trivial on the inertia group at $v$, and $0$ otherwise; for a non-zero ideal $I$ of $\mathcal{O}_K$ let [`ArtinL.Abelian.idealValue`](def/ArtinL_Abelian.html#L39) $\psi\,I$ be the (finitely supported) product over all primes $v$ of $\mathrm{localValue}(\psi,v)$ raised to the multiplicity of $v$ in $I$; let the Dirichlet coefficient [`ArtinL.Abelian.coeff`](def/ArtinL_Abelian.html#L43) $\psi\,n$ be $0$ for $n = 0$ and otherwise the sum of $\mathrm{idealValue}(\psi, I)$ over the finitely many ideals $I$ of absolute norm $n$; and let [`ArtinL.Abelian.LSeries`](def/ArtinL_Abelian.html#L46) $\psi\,s$ be the $L$-series $\sum_{n} \mathrm{coeff}(\psi,n) n^{-s}$ of these coefficients. The theorem asserts three things at such an $s$: the series is `LSeriesSummable`, i.e. $n \mapsto \mathrm{coeff}(\psi,n) n^{-s}$ is summable; its sum is non-zero; and the family of local factors $\bigl(1 - \mathrm{localValue}(\psi,v)\,(\mathrm{absNorm}\,v)^{-s}\bigr)^{-1}$, indexed by the non-zero primes $v$ of $\mathcal{O}_K$, has unconditional product (in the sense of `HasProd`) equal to that sum.
--
--   This is the elementary analytic input for abelian Artin $L$-series over a number field: absolute convergence, the Euler product over the finite places, and non-vanishing in the half-plane $\operatorname{Re} s > 1$. It is used downstream to rewrite the $L$-series as a product over places above a given prime, to produce the completed $L$-series and its functional equation for odd characters, and to compare an $L$-series with a product of character $L$-series coming from a trace identity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ArtinL_Abelian_lSeriesSummable_and_lSeries_ne_zero_and_hasProd.lean

import Mathlib
import Definitions.Def_ArtinL_Abelian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

universe u v

theorem ArtinL.Abelian.lSeriesSummable_and_lSeries_ne_zero_and_hasProd
    (K : Type u) (M : Type v) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsGalois K M] (ψ : (M ≃ₐ[K] M) →* ℂˣ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (ArtinL.Abelian.coeff ψ) s ∧ ArtinL.Abelian.LSeries ψ s ≠ 0 ∧
      HasProd (fun v : HeightOneSpectrum (𝓞 K) =>
        (1 - ArtinL.Abelian.localValue ψ v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹)
        (ArtinL.Abelian.LSeries ψ s) := by sorry
