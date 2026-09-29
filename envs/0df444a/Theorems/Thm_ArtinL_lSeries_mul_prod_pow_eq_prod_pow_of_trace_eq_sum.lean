-- Prove2me | Theorems.Thm_ArtinL_lSeries_mul_prod_pow_eq_prod_pow_of_trace_eq_sum
-- name    : ArtinL.lSeries_mul_prod_pow_eq_prod_pow_of_trace_eq_sum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/63e4cbfd-51fa-54ce-b929-2cdfc12be1b8
-- title:
--   Artin L-series and induced characters on Re s>1
-- statement:
--   Fix $n,k\in\mathbb N$, a monoid homomorphism $\rho$ from $\Gamma_{\mathbb Q}=\operatorname{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ (the $\mathbb Q$-algebra automorphisms of `AlgebraicClosure ℚ`) to $\mathrm{GL}_n(\mathbb C)$, and an intermediate field $F$ of $\overline{\mathbb Q}/\mathbb Q$ which is a number field and Galois over $\mathbb Q$. Assume $\rho$ factors as $\rho = \rho_F\circ\operatorname{res}_F$, where $\rho_F\colon \operatorname{Gal}(F/\mathbb Q)\to \mathrm{GL}_n(\mathbb C)$ is a monoid homomorphism and $\operatorname{res}_F$ is `AlgEquiv.restrictNormalHom F`. Given subgroups $H_i\le \operatorname{Gal}(F/\mathbb Q)$, homomorphisms $\chi_i\colon H_i\to\mathbb C^\times$ and integers $a_i$ for $i\in\{0,\dots,k-1\}$, assume the trace identity $\operatorname{tr}\rho_F(g)=\sum_i a_i\,|H_i|^{-1}\sum_{x\in\operatorname{Gal}(F/\mathbb Q)}\chi_i(x^{-1}gx)$ for all $g$, the inner summand being $0$ when $x^{-1}gx\notin H_i$; this is Frobenius' formula expressing $\operatorname{tr}\rho_F$ as the integral combination $\sum_i a_i\operatorname{Ind}_{H_i}^{\operatorname{Gal}(F/\mathbb Q)}\chi_i$. Let $s\in\mathbb C$ with $\operatorname{Re} s>1$. Write $L(\rho,s)$ for the Dirichlet series $\sum_{m\ge 1}\operatorname{coeff}(\rho)(m)m^{-s}$, whose $m$-th coefficient is the product over the prime factorisation $m=\prod p^{e}$ of the $e$-th power-series coefficient of the inverse of the Euler-factor polynomial [`ArtinL.eulerFactor`](def/ArtinL_EulerFactor.html#L86) $\rho\,p$; and write $L(\psi_i,s)$ for the abelian Artin $L$-series $\sum_{m\ge1}\bigl(\sum_{\mathfrak a,\,N\mathfrak a=m}\psi_i(\mathfrak a)\bigr)m^{-s}$ over $K_i=F^{H_i}$ attached by [`ArtinL.Abelian.ofSubgroup`](def/ArtinL_Abelian.html#L94) to $\chi_i$ viewed, via $\operatorname{Gal}(F/K_i)\cong H_i$, as a character $\psi_i$ of $\operatorname{Gal}(F/K_i)$, where $\psi_i(\mathfrak a)$ is the multiplicative extension of the local values [`ArtinL.Abelian.localValue`](def/ArtinL_Abelian.html#L36) to ideals. The conclusion is $$L(\rho,s)\cdot\prod_i L(\psi_i,s)^{\max(-a_i,0)}=\prod_i L(\psi_i,s)^{\max(a_i,0)},$$ the integer powers being taken in the truncated form $(-a_i)^+$ and $a_i^+$; equivalently $L(\rho,s)=\prod_i L(\psi_i,s)^{a_i}$.
--
--   This is Artin's theorem that his $L$-series are multiplicative in the character and invariant under induction, stated on the half-plane $\operatorname{Re} s>1$ in the form in which it combines with Brauer's induction theorem: once $\operatorname{tr}\rho_F$ is written as an integral combination of monomial characters, $L(\rho,s)$ becomes a product of integral powers of abelian (Hecke) $L$-series. It is used in the derivation of the analytic continuation and functional equation for the completed $L$-series of an odd two-dimensional representation, via [`ArtinL.exists_completedLSeries_functionalEquation_of_odd`](thm.html#ArtinL.exists_completedLSeries_functionalEquation_of_odd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ArtinL_lSeries_mul_prod_pow_eq_prod_pow_of_trace_eq_sum.lean

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

theorem ArtinL.lSeries_mul_prod_pow_eq_prod_pow_of_trace_eq_sum {n : ℕ} (ρ : Γℚ →* GL (Fin n) ℂ)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField F] [IsGalois ℚ F]
    (ρF : (F ≃ₐ[ℚ] F) →* GL (Fin n) ℂ) (hρ : ρ = ρF.comp (AlgEquiv.restrictNormalHom F))
    {k : ℕ} (H : Fin k → Subgroup (F ≃ₐ[ℚ] F)) (χ : (i : Fin k) → (H i →* ℂˣ)) (a : Fin k → ℤ)
    (htr : ∀ g : F ≃ₐ[ℚ] F, ((ρF g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace =
      ∑ i : Fin k, (a i : ℂ) * ((Nat.card (H i) : ℂ)⁻¹ *
        ∑ x : F ≃ₐ[ℚ] F,
          if hx : x⁻¹ * g * x ∈ H i then (((χ i) ⟨x⁻¹ * g * x, hx⟩ : ℂˣ) : ℂ) else 0))
    {s : ℂ} (hs : 1 < s.re) :
    _root_.LSeries (ArtinL.coeff ρ) s *
        ∏ i, ArtinL.Abelian.LSeries (ArtinL.Abelian.ofSubgroup (H i) (χ i)) s ^ (-a i).toNat =
      ∏ i, ArtinL.Abelian.LSeries (ArtinL.Abelian.ofSubgroup (H i) (χ i)) s ^ (a i).toNat := by sorry
