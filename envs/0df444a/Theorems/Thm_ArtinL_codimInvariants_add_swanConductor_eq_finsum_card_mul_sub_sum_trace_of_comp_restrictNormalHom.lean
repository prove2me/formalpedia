-- Prove2me | Theorems.Thm_ArtinL_codimInvariants_add_swanConductor_eq_finsum_card_mul_sub_sum_trace_of_comp_restrictNormalHom
-- name    : ArtinL.codimInvariants_add_swanConductor_eq_finsum_card_mul_sub_sum_trace_of_comp_restrictNormalHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/78e33237-b451-5b5c-b6aa-8bfbf6157677
-- title:
--   Rational Artin conductor exponent as a character sum
-- statement:
--   Let $n$ be a natural number and $\rho\colon \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)\to \mathrm{GL}_n(\mathbb C)$ a group homomorphism, where $\overline{\mathbb Q}$ is the chosen algebraic closure of $\mathbb Q$. Let $F$ be an intermediate field of $\overline{\mathbb Q}/\mathbb Q$ which is a number field and Galois over $\mathbb Q$, and let $\rho_F\colon (F\simeq_{\mathbb Q}F)\to \mathrm{GL}_n(\mathbb C)$ satisfy $\rho=\rho_F\circ\mathrm{res}$, $\mathrm{res}$ being `AlgEquiv.restrictNormalHom F`. Let $p$ be a prime, $A$ a valuation subring of $\overline{\mathbb Q}$ in which the image of $p$ is a non-unit, and $\mathfrak P$ a maximal ideal of $\mathcal O_F$ whose contraction to $\mathbb Z$ is $(p)$. Put $I_A=(A.\mathrm{inertiaSubgroup}\ \mathbb Q)$ pushed into $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ along the decomposition subgroup, and for $i\ge 0$ let $R_i$ be the intersection of $I_A$ with the image in the decomposition subgroup of the $i$-th lower ramification group of the local ring `placeUnder ρ A`. For a subgroup $H$ write $c(H)=n-\dim_{\mathbb C}(\mathbb C^n)^{H}$ (truncated subtraction), the invariants being those of the matrix representation attached to $\rho$ restricted to $H$. The assertion is that the rational number $$c(I_A)+\sum_{i}^{\mathrm{f}}\frac{\#\rho(R_{i+1})}{\#\rho(I_A)}\,c(R_{i+1}),$$ viewed in $\mathbb C$, equals $$\sum_{j}^{\mathrm{f}}\frac{\#G_j}{\#G_0}\Bigl(n-\frac1{\#G_j}\sum_{g\in G_j}\operatorname{tr}\rho_F(g)\Bigr),$$ where $G_j=(\mathfrak P^{j+1}).\mathrm{inertia}\,(F\simeq_{\mathbb Q}F)$ and $G_0=(\mathfrak P^{1}).\mathrm{inertia}\,(F\simeq_{\mathbb Q}F)$; both sums are finitely supported sums over $\mathbb N$.
--
--   This is the unrounded Artin conductor exponent of $\rho$ at $p$ — the codimension of the inertia invariants plus the Swan term — expressed as a character sum over the lower ramification filtration of any prime $\mathfrak P$ of $\mathcal O_F$ above $p$, for any finite Galois level $F$ through which $\rho$ factors; in particular the right-hand side is independent of the choice of place $A$ above $p$. It is used in [`ArtinL.conductor_mul_prod_pow_eq_prod_pow_of_trace_eq_sum`](thm.html#ArtinL.conductor_mul_prod_pow_eq_prod_pow_of_trace_eq_sum) to compare conductors of representations with equal traces.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ArtinL_codimInvariants_add_swanConductor_eq_finsum_card_mul_sub_sum_trace_of_comp_restrictNormalHom.lean

import Mathlib
import Definitions.Def_ArtinL_Conductor
import Definitions.Def_ArtinL_Abelian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open NumberField

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
open scoped Classical in

theorem ArtinL.codimInvariants_add_swanConductor_eq_finsum_card_mul_sub_sum_trace_of_comp_restrictNormalHom {n : ℕ} (ρ : Γℚ →* GL (Fin n) ℂ)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField F] [IsGalois ℚ F]
    (ρF : (F ≃ₐ[ℚ] F) →* GL (Fin n) ℂ) (hρ : ρ = ρF.comp (AlgEquiv.restrictNormalHom F))
    (p : ℕ) (hp : p.Prime) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : ((p : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits)
    (𝔓 : Ideal (𝓞 F)) [𝔓.IsMaximal] (h𝔓 : 𝔓.under ℤ = Ideal.span {(p : ℤ)}) :
    (((ArtinL.codimInvariants ρ (A.inertiaSubgroupIn ℚ) : ℚ) + ArtinL.swanConductor ρ A : ℚ) : ℂ) =
      ∑ᶠ j : ℕ, ((Nat.card ((𝔓 ^ (j + 1)).inertia (F ≃ₐ[ℚ] F)) : ℂ) /
          (Nat.card ((𝔓 ^ 1).inertia (F ≃ₐ[ℚ] F)) : ℂ)) *
        ((n : ℂ) - ((Nat.card ((𝔓 ^ (j + 1)).inertia (F ≃ₐ[ℚ] F)) : ℂ))⁻¹ *
          ∑ g : ↥((𝔓 ^ (j + 1)).inertia (F ≃ₐ[ℚ] F)),
            ((ρF (g : F ≃ₐ[ℚ] F) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace) := by sorry
