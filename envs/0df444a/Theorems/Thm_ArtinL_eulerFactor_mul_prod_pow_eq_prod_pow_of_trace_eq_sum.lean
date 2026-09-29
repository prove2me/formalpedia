-- Prove2me | Theorems.Thm_ArtinL_eulerFactor_mul_prod_pow_eq_prod_pow_of_trace_eq_sum
-- name    : ArtinL.eulerFactor_mul_prod_pow_eq_prod_pow_of_trace_eq_sum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/6d2c0efb-9633-5ba1-ad28-27de9bb70808
-- title:
--   Artin's Euler factor at p from induced characters
-- statement:
--   Let $n,k\in\mathbb N$, let $\rho$ be a monoid homomorphism from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$, realised as the automorphism group of `AlgebraicClosure ℚ` over $\mathbb Q$, to $\mathrm{GL}_n(\mathbb C)$, and let $F$ be an intermediate field of $\overline{\mathbb Q}/\mathbb Q$ that is a number field and Galois over $\mathbb Q$. Assume $\rho$ factors as $\rho=\rho_F\circ\mathrm{res}_F$ for a homomorphism $\rho_F\colon\mathrm{Gal}(F/\mathbb Q)\to\mathrm{GL}_n(\mathbb C)$. Let $H_i\le\mathrm{Gal}(F/\mathbb Q)$ be subgroups, $\chi_i\colon H_i\to\mathbb C^\times$ homomorphisms and $a_i\in\mathbb Z$, for $i\in\{0,\dots,k-1\}$, and assume the character identity: for every $g\in\mathrm{Gal}(F/\mathbb Q)$ the trace of the matrix $\rho_F(g)$ equals $\sum_i a_i\,|H_i|^{-1}\sum_{x\in\mathrm{Gal}(F/\mathbb Q)}\chi_i(x^{-1}gx)$, the inner summand being $0$ when $x^{-1}gx\notin H_i$ (Frobenius' formula for $\sum_i a_i\,\mathrm{Ind}_{H_i}^{G}\chi_i$). Let $p$ be a prime. For each $i$ put $$E_i:=\prod^{\mathrm f}_{v}\bigl(1-C(\lambda_i(v))\,X^{f(v\mid p)}\bigr)\in\mathbb C[X],$$ the finite-support product over the height-one primes $v$ of $\mathcal O_{F^{H_i}}$, the factor being $1$ unless $p\in v$, where $f(v\mid p)$ is `inertiaDeg'` of $v$ over $p\mathbb Z$ and $\lambda_i(v)$ is the local value at $v$ of the character $\mathrm{Gal}(F/F^{H_i})\to\mathbb C^\times$ induced by $\chi_i$ through the identification of the fixing subgroup of $F^{H_i}$ with $H_i$: namely its value at the arithmetic Frobenius `artinFrob` at $v$ if the character is trivial on the inertia group at $v$, and $0$ otherwise. The conclusion is $$\mathrm{eulerFactor}(\rho,p)\cdot\prod_i E_i^{(-a_i)^+}=\prod_i E_i^{(a_i)^+},$$ with exponents the natural-number truncations of $-a_i$ and $a_i$, and $\mathrm{eulerFactor}(\rho,p)$ defined as follows: if some valuation subring $A$ of $\overline{\mathbb Q}$ has $p$ in its nonunits and some $\sigma$ lies in the decomposition subgroup of $A$ and acts on the residue field of $A$ by $x\mapsto x^p$, then it is the reversed characteristic polynomial of $\sigma$ acting on the inertia invariants of $\rho$ at $A$ (and $1$ if $\sigma$ fails to preserve those invariants); otherwise it is $1$.
--
--   This is the prime-by-prime form of Artin's factorisation of an Artin $L$-function along a virtual decomposition of its character into induced characters of one-dimensional characters of subgroups: the local factor of $\rho$ at $p$ is expressed through the local factors at $p$ of the abelian (Hecke) $L$-functions attached to the $\chi_i$ over the fixed fields $F^{H_i}$. It is used to derive the corresponding identity of $L$-series, [`ArtinL.lSeries_mul_prod_pow_eq_prod_pow_of_trace_eq_sum`](thm.html#ArtinL.lSeries_mul_prod_pow_eq_prod_pow_of_trace_eq_sum).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ArtinL_eulerFactor_mul_prod_pow_eq_prod_pow_of_trace_eq_sum.lean

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

theorem ArtinL.eulerFactor_mul_prod_pow_eq_prod_pow_of_trace_eq_sum {n : ℕ} (ρ : Γℚ →* GL (Fin n) ℂ)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField F] [IsGalois ℚ F]
    (ρF : (F ≃ₐ[ℚ] F) →* GL (Fin n) ℂ) (hρ : ρ = ρF.comp (AlgEquiv.restrictNormalHom F))
    {k : ℕ} (H : Fin k → Subgroup (F ≃ₐ[ℚ] F)) (χ : (i : Fin k) → (H i →* ℂˣ)) (a : Fin k → ℤ)
    (htr : ∀ g : F ≃ₐ[ℚ] F, ((ρF g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace =
      ∑ i : Fin k, (a i : ℂ) * ((Nat.card (H i) : ℂ)⁻¹ *
        ∑ x : F ≃ₐ[ℚ] F,
          if hx : x⁻¹ * g * x ∈ H i then (((χ i) ⟨x⁻¹ * g * x, hx⟩ : ℂˣ) : ℂ) else 0))
    {p : ℕ} (hp : p.Prime) :
    ArtinL.eulerFactor ρ p *
        ∏ i, (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField (H i))),
            if ((p : ℕ) : 𝓞 ↥(IntermediateField.fixedField (H i))) ∈ v.asIdeal then
              (1 - Polynomial.C (ArtinL.Abelian.localValue (ArtinL.Abelian.ofSubgroup (H i) (χ i)) v) *
                Polynomial.X ^ (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal : Polynomial ℂ)
            else 1) ^ (-a i).toNat =
      ∏ i, (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField (H i))),
            if ((p : ℕ) : 𝓞 ↥(IntermediateField.fixedField (H i))) ∈ v.asIdeal then
              (1 - Polynomial.C (ArtinL.Abelian.localValue (ArtinL.Abelian.ofSubgroup (H i) (χ i)) v) *
                Polynomial.X ^ (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal : Polynomial ℂ)
            else 1) ^ (a i).toNat := by sorry
