-- Prove2me | Theorems.Thm_DiazModulus_coprime_pencil_of_degree_le_two_normal_form
-- name    : DiazModulus.coprime_pencil_of_degree_le_two_normal_form
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-18T14:27:56.904668+00:00
-- url     : https://prove2.me/theorems/e07a91db-6ad9-4b2c-b8e3-63502dccade0
-- title:
--   The span of two coprime polynomials of degree at most two, not both constant, is span(1, X), span(1, X² + αX), span(X, X² + β) or span(X + β, X² + γX)
-- statement:
--   Let $K$ be a field and $a_0, a_1 \in K[X]$ coprime with $1 \leq \max(\deg a_0, \deg a_1) \leq 2$. Then $\mathrm{span}_K(a_0, a_1) = \mathrm{span}_K(p, q)$ for a pair $(p, q)$ of one of the forms
--
--   - $(1, X)$;
--   - $(1, X^2 + \alpha X)$ with $\alpha \in K$;
--   - $(X, X^2 + \beta)$ with $\beta \neq 0$;
--   - $(X + \beta, X^2 + \gamma X)$ with $\beta \neq 0$ and $\gamma \neq \beta$.
--
--   **Proof.** Coprimality makes $a_0, a_1$ linearly independent, so $P = \mathrm{span}(a_0, a_1)$ is a plane. If neither has an $X^2$ term, $P \subseteq \mathrm{span}(1, X)$ and the two are equal by dimension. Otherwise $P$ contains a monic $f = X^2 + dX + e$ and a non-zero $r$ of degree at most one (the combination of $a_0, a_1$ that kills the $X^2$ terms): if $r$ is constant, $P = \mathrm{span}(1, X^2 + dX)$; otherwise $X + \beta \in P$, and $P = \mathrm{span}(X, X^2 + e)$ with $e \neq 0$ when $\beta = 0$, or $P = \mathrm{span}(X + \beta, X^2 + \gamma X)$ with $\gamma = d - e/\beta \neq \beta$ when $\beta \neq 0$, the inequalities because $X$, resp. $X + \beta$, is not a common factor. Each equality holds because two polynomials of distinct degrees in $P$ span the plane $P$.
--
--   **Novelty.** An elementary fact about polynomials over a field; routine.
-- source:
--   Not found in the sources read in this form; elementary. R18 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 18 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem coprime_pencil_of_degree_le_two_normal_form (K : Type*) [Field K] (a₀ a₁ : K[X])
    (hcop : IsCoprime a₀ a₁) (hdeg : 1 ≤ max a₀.natDegree a₁.natDegree)
    (hdeg2 : max a₀.natDegree a₁.natDegree ≤ 2) :
    ∃ p q : K[X], Submodule.span K ({a₀, a₁} : Set K[X]) = Submodule.span K ({p, q} : Set K[X]) ∧
      ((p = 1 ∧ q = X) ∨ (∃ α : K, p = 1 ∧ q = X ^ 2 + C α * X) ∨
        (∃ β : K, β ≠ 0 ∧ p = X ∧ q = X ^ 2 + C β) ∨
        (∃ β γ : K, β ≠ 0 ∧ γ ≠ β ∧ p = X + C β ∧ q = X ^ 2 + C γ * X)) := by
  sorry

end DiazModulus
