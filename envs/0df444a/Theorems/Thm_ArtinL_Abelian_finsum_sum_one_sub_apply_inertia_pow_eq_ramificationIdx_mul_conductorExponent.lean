-- Prove2me | Theorems.Thm_ArtinL_Abelian_finsum_sum_one_sub_apply_inertia_pow_eq_ramificationIdx_mul_conductorExponent
-- name    : ArtinL.Abelian.finsum_sum_one_sub_apply_inertia_pow_eq_ramificationIdx_mul_conductorExponent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/4015ac1e-b031-5169-abba-5cba0027ba37
-- title:
--   Character sum over lower ramification groups at Q
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a Galois extension of $K$, let $\psi \colon \mathrm{Gal}(L/K) \to \mathbb{C}^{\times}$ be a homomorphism of monoids into the unit group of $\mathbb{C}$, let $w$ be a height-one prime of $\mathcal{O}_K$, and let $Q$ be a maximal ideal of $\mathcal{O}_L$ whose contraction to $\mathcal{O}_K$ is the ideal underlying $w$. For each $j \in \mathbb{N}$ let $(Q^{j+1}).\mathrm{inertia}$ denote the subgroup of $\mathrm{Gal}(L/K)$ of elements acting trivially on $\mathcal{O}_L/Q^{j+1}$, i.e. the $j$-th lower ramification group at $Q$. The assertion is the identity in $\mathbb{C}$ $$\sum_{j \in \mathbb{N}} \ \sum_{t \in (Q^{j+1}).\mathrm{inertia}} \bigl(1 - \psi(t)\bigr) \;=\; e \cdot f,$$ where the outer sum is a finsum over $\mathbb{N}$ (the inner sums vanish for all but finitely many $j$), $e$ is the ramification index of $w$ in $Q$ and $f$ is the natural number $\mathrm{conductorExponent}\,\psi\,w$, defined as $1$ or $0$ according as $\psi$ is or is not nontrivial on the inertia group $\mathrm{inertiaGroup}\,K\,L\,w$, plus the ceiling of the rational number $\mathrm{swanConductor}\,\psi\,w = \sum_{i \in \mathbb{N}} \bigl(\#\mathrm{ramificationGroup}\,K\,L\,w\,(i+1)/\#\mathrm{inertiaGroup}\,K\,L\,w\bigr)\cdot[\psi \ne 1 \text{ on } \mathrm{ramificationGroup}\,K\,L\,w\,(i+1)]$; the product $e \cdot f$ is formed in $\mathbb{N}$ and then cast to $\mathbb{C}$.
--
--   This is Artin's expression for the conductor exponent of a one-dimensional character as a sum over the lower ramification groups, here at an arbitrary maximal ideal $Q$ of $\mathcal{O}_L$ above $w$ rather than at a fixed chosen prime; the passage between the two uses conjugacy of the ramification groups at primes above $w$, and the absence of rounding in the Swan term reflects the integrality of the Swan conductor of an abelian character. It is used in the derivation of the conductor–discriminant formula, in [`ArtinL.finsum_card_mul_sub_sum_induced_eq_factorization_discr_mul_absNorm_conductor`](thm.html#ArtinL.finsum_card_mul_sub_sum_induced_eq_factorization_discr_mul_absNorm_conductor).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ArtinL_Abelian_finsum_sum_one_sub_apply_inertia_pow_eq_ramificationIdx_mul_conductorExponent.lean

import Mathlib
import Definitions.Def_ArtinL_Abelian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField
open scoped Classical in

theorem ArtinL.Abelian.finsum_sum_one_sub_apply_inertia_pow_eq_ramificationIdx_mul_conductorExponent
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (ψ : (L ≃ₐ[K] L) →* ℂˣ) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (Q : Ideal (𝓞 L)) [Q.IsMaximal]
    (hQ : Q.under (𝓞 K) = w.asIdeal) :
    ∑ᶠ j : ℕ, ∑ t : ↥((Q ^ (j + 1)).inertia (L ≃ₐ[K] L)), (1 - ((ψ (t : L ≃ₐ[K] L) : ℂˣ) : ℂ)) =
      ((w.asIdeal.ramificationIdx' Q * ArtinL.Abelian.conductorExponent ψ w : ℕ) : ℂ) := by sorry
