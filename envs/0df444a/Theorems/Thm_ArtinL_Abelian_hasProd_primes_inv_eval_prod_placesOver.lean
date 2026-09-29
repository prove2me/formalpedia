-- Prove2me | Theorems.Thm_ArtinL_Abelian_hasProd_primes_inv_eval_prod_placesOver
-- name    : ArtinL.Abelian.hasProd_primes_inv_eval_prod_placesOver
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/6d2816f1-c1b0-5918-9561-56bc11f247f1
-- title:
--   Abelian Artin L-series as Euler product over rational primes
-- statement:
--   Let $K$ and $M$ be number fields with $M$ an extension of $K$ that is Galois, let $\psi\colon \mathrm{Gal}(M/K)\to\mathbb{C}^{\times}$ be a group homomorphism into the units of $\mathbb{C}$, and let $s\in\mathbb{C}$ satisfy $\operatorname{Re} s>1$. For a height one prime $v$ of $\mathcal{O}_K$ write $c_v=\psi(\sigma_v)$, where $\sigma_v$ is the arithmetic Frobenius attached to a chosen prime of $\mathcal{O}_M$ above $v$, whenever $\psi$ is trivial on the inertia group at $v$, and $c_v=0$ otherwise. For each rational prime $p$ form the polynomial $E_p(X)\in\mathbb{C}[X]$ as the (finite, in the sense of a `finprod`) product over all height one primes $v$ of $\mathcal{O}_K$ of the factor $1-c_v X^{f(v\mid p)}$ if the image of $p$ in $\mathcal{O}_K$ lies in $v$, and of $1$ otherwise, where $f(v\mid p)$ is the inertia degree of $v$ over the ideal $(p)\subseteq\mathbb{Z}$. The assertion is that the family $p\mapsto E_p\bigl(p^{-s}\bigr)^{-1}$, indexed by the rational primes, is multipliable with product equal to $\sum_{n\ge 1} a_n n^{-s}$, where $a_n$ is the sum of the values $\psi$ assigns to the ideals of $\mathcal{O}_K$ of absolute norm $n$ (the $L$-series of $\psi$).
--
--   This is the Euler product of an abelian Artin $L$-series in the form where the local factors are grouped fibre by fibre over the rational primes, the $p$-factor being the inverse of $\prod_{v\mid p}(1-\psi(v)X^{f(v\mid p)})$ evaluated at $X=p^{-s}$. It is a regrouping of the absolutely convergent Euler product over the primes of $\mathcal{O}_K$ provided by [`ArtinL.Abelian.lSeriesSummable_and_lSeries_ne_zero_and_hasProd`](thm.html#ArtinL.Abelian.lSeriesSummable_and_lSeries_ne_zero_and_hasProd), and it is the shape in which abelian $L$-series enter Artin's prime-by-prime factorisation of the $L$-series of a representation, used by [`ArtinL.lSeries_mul_prod_pow_eq_prod_pow_of_trace_eq_sum`](thm.html#ArtinL.lSeries_mul_prod_pow_eq_prod_pow_of_trace_eq_sum).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ArtinL_Abelian_hasProd_primes_inv_eval_prod_placesOver.lean

import Mathlib
import Definitions.Def_ArtinL_EulerFactor
import Definitions.Def_ArtinL_Abelian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open NumberField

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
open scoped Classical in

theorem ArtinL.Abelian.hasProd_primes_inv_eval_prod_placesOver
    (K : Type) (M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsGalois K M] (ψ : (M ≃ₐ[K] M) →* ℂˣ) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes =>
        ((∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
            if ((p : ℕ) : 𝓞 K) ∈ v.asIdeal then
              (1 - Polynomial.C (ArtinL.Abelian.localValue ψ v) *
                Polynomial.X ^ (Ideal.span {((p : ℕ) : ℤ)}).inertiaDeg' v.asIdeal : Polynomial ℂ)
            else 1).eval ((p : ℂ) ^ (-s)))⁻¹)
      (ArtinL.Abelian.LSeries ψ s) := by sorry
