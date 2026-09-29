-- Prove2me | Theorems.Thm_ArtinL_Abelian_factorization_absNorm_conductor_eq_finsum_inertiaDeg_mul_conductorExponent
-- name    : ArtinL.Abelian.factorization_absNorm_conductor_eq_finsum_inertiaDeg_mul_conductorExponent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/448eb88f-c109-5241-bdd1-41df71dc025e
-- title:
--   p-adic valuation of the norm of the abelian conductor
-- statement:
--   Let $K$ and $L$ be number fields with $L$ an algebra over $K$ whose extension is Galois, let $\psi \colon (L \simeq_{\mathrm{alg}[K]} L) \to \mathbb{C}^{\times}$ be a monoid homomorphism from the Galois group to the units of $\mathbb{C}$, and let $p$ be a prime natural number. Attached to $\psi$ is the ideal [`ArtinL.Abelian.conductor`](def/ArtinL_Abelian.html#L57) $\psi$ of $\mathcal{O}_K$, defined as the (finitely supported) product over the height-one primes $v$ of $\mathcal{O}_K$ of $v^{e(\psi,v)}$, where the exponent $e(\psi,v) =$ [`ArtinL.Abelian.conductorExponent`](def/ArtinL_Abelian.html#L54) $\psi\, v$ is $1$ unless $\psi$ is trivial on the whole inertia group at $v$ (in which case it is $0$), plus the ceiling, as a natural number, of the Swan conductor $\sum_{i \ge 0} \bigl(\#G_{i+1}/\#G_0\bigr)\cdot[\psi \text{ is nontrivial on } G_{i+1}]$, the $G_i$ being the ramification groups at $v$ and $G_0$ the inertia group. The theorem asserts that the exponent of $p$ in the prime factorisation of the natural number $\mathrm{absNorm}$ of this conductor equals the finite sum, over all height-one primes $w$ of $\mathcal{O}_K$, of $f(w\mid p)\cdot e(\psi,w)$ if the image of $p$ in $\mathcal{O}_K$ lies in $w$ and $0$ otherwise, where $f(w\mid p)$ is the inertia degree `inertiaDeg'` of $w$ over the ideal $p\mathbb{Z}$.
--
--   This is the local–global bookkeeping identity $v_p\bigl(N\mathfrak{f}(\psi)\bigr) = \sum_{w \mid p} f(w\mid p)\, f(\psi,w)$ for the absolute norm of an abelian Artin conductor, resting on multiplicativity of the absolute norm and on $N w = p^{f(w\mid p)}$. It feeds the conductor–discriminant computation [`ArtinL.finsum_card_mul_sub_sum_induced_eq_factorization_discr_mul_absNorm_conductor`](thm.html#ArtinL.finsum_card_mul_sub_sum_induced_eq_factorization_discr_mul_absNorm_conductor), and thence the shape of the analytic conductor of abelian Artin $L$-functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ArtinL_Abelian_factorization_absNorm_conductor_eq_finsum_inertiaDeg_mul_conductorExponent.lean

import Mathlib
import Definitions.Def_ArtinL_Abelian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField
open scoped Classical in

theorem ArtinL.Abelian.factorization_absNorm_conductor_eq_finsum_inertiaDeg_mul_conductorExponent
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (ψ : (L ≃ₐ[K] L) →* ℂˣ) (p : ℕ) (hp : p.Prime) :
    (Ideal.absNorm (ArtinL.Abelian.conductor ψ)).factorization p =
      ∑ᶠ w : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        if ((p : ℕ) : 𝓞 K) ∈ w.asIdeal then
          (Ideal.span {(p : ℤ)}).inertiaDeg' w.asIdeal * ArtinL.Abelian.conductorExponent ψ w
        else 0 := by sorry
