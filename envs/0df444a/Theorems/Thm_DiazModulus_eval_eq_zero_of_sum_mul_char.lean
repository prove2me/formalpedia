-- Prove2me | Theorems.Thm_DiazModulus_eval_eq_zero_of_sum_mul_char
-- name    : DiazModulus.eval_eq_zero_of_sum_mul_char
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-30T09:51:33.970871+00:00
-- url     : https://prove2.me/theorems/83160726-8ecf-4fed-94b5-97fb3ddd000a
-- title:
--   Generalised Dedekind lemma: a vanishing combination of distinct characters of a commutative group with polynomial coefficients along a homomorphism has vanishing coefficients
-- statement:
--   Let $\Gamma$ be a commutative group, $A_0$ a type, $\iota$ a finite type, $\rho$ a homomorphism from $\Gamma$ to the additive group $\mathbb{C}^{A_0}$ (`Γ →* Multiplicative (A₀ → ℂ)`), $\chi_c : \Gamma \to \mathbb{C}^\times$ ($c \in \iota$) pairwise distinct characters, and $F_c \in \mathbb{C}[X_{A_0}]$. If $\sum_c F_c(\rho(g))\,\chi_c(g) = 0$ for every $g \in \Gamma$, then $F_c(\rho(g)) = 0$ for every $c$ and every $g$.
--
--   **Proof.** By finite differences: $g \mapsto F(\rho(g))$ has finite difference degree, while a non-zero multiple of a non-trivial character has none. Induction on the set of characters and, inside it, on the degree of one coefficient, applied to the translated relation.
--
--   **Novelty.** Classical; routine formalisation. A form of Dedekind's lemma with polynomial coefficients along a homomorphism.
-- source:
--   Classical: Dedekind's (Artin's) lemma on the linear independence of characters, here with coefficients that are polynomials along an additive homomorphism. C1.3 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 30 October 2026 (C. Perassi).

import Mathlib

namespace DiazModulus

theorem eval_eq_zero_of_sum_mul_char {Γ A₀ ι : Type*} [CommGroup Γ] [Fintype ι]
    (ρ : Γ →* Multiplicative (A₀ → ℂ)) (χ : ι → Γ →* ℂˣ) (hχ : Function.Injective χ)
    (F : ι → MvPolynomial A₀ ℂ)
    (h : ∀ g, ∑ c, MvPolynomial.eval (Multiplicative.toAdd (ρ g)) (F c) * (χ c g : ℂ) = 0) :
    ∀ c g, MvPolynomial.eval (Multiplicative.toAdd (ρ g)) (F c) = 0 := by
  sorry

end DiazModulus
