-- Prove2me | Theorems.Thm_DiazModulus_isAlgebraic_of_hyperbola_pair_not_algebraicIndependent
-- name    : DiazModulus.isAlgebraic_of_hyperbola_pair_not_algebraicIndependent
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-18T17:47:18.214038+00:00
-- url     : https://prove2.me/theorems/6c9029fe-9e52-42e8-a46b-108ff8056d72
-- title:
--   The hyperbola step: if u is transcendental over F ⊆ ℂ with uū ∈ F, c₁, c₂ ∈ F, and c₁ + u, c₂ + ū are algebraically dependent, then c₁ and c₂ are algebraic
-- statement:
--   Let $F$ be a subfield of $\mathbb{C}$ and $u \in \mathbb{C}$ transcendental over $F$ with $u\bar u \in F$, and let $c_1, c_2 \in F$. If the pair $(c_1 + u, c_2 + \bar u)$ is not algebraically independent over $\mathbb{Q}$, then $c_1$ and $c_2$ are algebraic.
--
--   **Proof.** By `DiazModulus.transcendental_add_mul_add_mul_conj`, $e_1 = c_1 + u$ is transcendental over $F$, hence over $\mathbb{Q}$, so the dependence makes $e_2 = c_2 + \bar u$ algebraic over $\mathbb{Q}[e_1]$ (`Transcendence.isAlgebraic_adjoin_of_not_algebraicIndependent_pair`): $\sum_{k \leq K} g_k(e_1)e_2^k = 0$ with $g_k \in \mathbb{Q}[X]$ and $g_K(e_1) \neq 0$. With $\rho = u\bar u \neq 0$, the polynomial $R(T) = \sum_k g_k(c_1 + T)(c_2T + \rho)^kT^{K-k}$ has coefficients in $F$ and $R(u) = u^K\sum_k g_k(e_1)e_2^k = 0$, since $c_2u + \rho = ue_2$. As $u$ is transcendental over $F$, $R = 0$, so $R(0) = g_K(c_1)\rho^K = 0$ and $c_1$ is algebraic, $g_K$ being non-zero. For $c_2$ the same argument is applied to $\bar u$, which is transcendental over $F$ by `DiazModulus.transcendental_add_mul_add_mul_conj` again, with $\bar u u = \rho$ and the swapped pair $(c_2 + \bar u, c_1 + u)$; no factorisation is needed.
--
--   **Novelty.** Not found in the sources read; routine.
-- source:
--   Not found in the sources read. Uses DiazModulus.transcendental_add_mul_add_mul_conj and Transcendence.isAlgebraic_adjoin_of_not_algebraicIndependent_pair. R19 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 18 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem isAlgebraic_of_hyperbola_pair_not_algebraicIndependent
    (F : Subfield ℂ) (u : ℂ) (hu : Transcendental F u) (hρ : u * conj u ∈ F)
    (c₁ c₂ : ℂ) (hc₁ : c₁ ∈ F) (hc₂ : c₂ ∈ F)
    (hdep : ¬ AlgebraicIndependent ℚ ![c₁ + u, c₂ + conj u]) :
    IsAlgebraic ℚ c₁ ∧ IsAlgebraic ℚ c₂ := by
  sorry

end DiazModulus
