-- Prove2me | Theorems.Thm_DiazModulus_sharp_four_and_strong_five_exponentials_of_strong_four
-- name    : DiazModulus.sharp_four_and_strong_five_exponentials_of_strong_four
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-01T14:41:21.362017+00:00
-- url     : https://prove2.me/theorems/4dd86423-9f18-4f44-80de-848cb622c49d
-- title:
--   The strong four exponentials conjecture, with Baker's theorem, implies the sharp four and the strong five exponentials conjectures
-- statement:
--   Here $\mathcal{L}$ is the set of logarithms of algebraic numbers, and $\widetilde{\mathcal{L}}$ is the $\overline{\mathbb{Q}}$-vector space spanned by $1$ and $\mathcal{L}$. The strong four exponentials conjecture (`DiazModulus.StrongFourExponentials`, Conjecture 11.17 of Waldschmidt's book) is carried as the hypothesis `hS`: if $x_1, x_2$ are linearly independent over $\overline{\mathbb{Q}}$ and so are $y_1, y_2$, then one of the four products $x_iy_j$ is not in $\widetilde{\mathcal{L}}$. Baker's theorem is carried as the hypothesis `hB`, in its two-logarithm inhomogeneous form, as in `DiazModulus.candidate_one_log_saturation`.
--
--   1. **Sharp four exponentials.** If $x_1, x_2$ are linearly independent over $\mathbb{Q}$ and so are $y_1, y_2$, and if $\beta_{ij}$ ($i, j = 1, 2$) are algebraic numbers such that the four numbers $e^{x_iy_j - \beta_{ij}}$ are algebraic, then $x_iy_j = \beta_{ij}$ for all $i, j$.
--   2. **Strong five exponentials.** Under the hypotheses of part 1 (with constants $\alpha_{ij}$), if moreover $\eta \neq 0$ and $\beta$ are algebraic and $e^{\eta x_2/x_1 - \beta}$ is algebraic, then also $\eta x_2 = \beta x_1$.
--
--   The two parts are stated in the forms of `DiazModulus.diaz_of_sharp_four_exponentials` and `DiazModulus.diaz_of_strong_five_exponentials`, so they can be passed to those nodes, to `DiazModulus.recip_pi_not_log_of_sharp_four_exponentials` and `DiazModulus.recip_pi_not_log_of_strong_five_exponentials`, and to `DiazModulus.exp_log_mul_log_transcendental_of_strong_five`.
--
--   **Proof.** The four products lie in $\widetilde{\mathcal{L}}$, so the conjecture makes $(x_1, x_2)$ or $(y_1, y_2)$ linearly dependent over $\overline{\mathbb{Q}}$. Say $x_2 = cx_1$, with $c$ algebraic and, by $\mathbb{Q}$-independence, not rational. For the logarithms $\ell_{ij} = x_iy_j - \beta_{ij}$, the number $\ell_{2j} - c\ell_{1j}$ is algebraic. Baker's theorem makes $\ell_{1j}$ and $\ell_{2j}$ linearly dependent over $\mathbb{Q}$; as $c \notin \mathbb{Q}$, both are then algebraic, hence $0$ by Hermite–Lindemann. The case $y_2 = dy_1$ runs along the rows. For part 2, $x_2/x_1 = \alpha_{21}/\alpha_{11}$ is algebraic, so $\eta x_2/x_1 - \beta$ is an algebraic logarithm of an algebraic number, hence $0$.
--
--   **Novelty.** None claimed. Part 2 from part 1 is Waldschmidt's remark (1988, p. 379) that the strong five exponentials conjecture is clearly weaker than the strong four exponentials conjecture of that paper. That conjecture is his Corollary 2.1 (the sharp six exponentials theorem) with two numbers $y_j$ instead of three (p. 377): part 1 here, called the sharp four exponentials conjecture in his 2005 survey. The strong four exponentials conjecture of his book is stated for products in $\widetilde{\mathcal{L}}$, the $\overline{\mathbb{Q}}$-span of $1$ and $\mathcal{L}$, rather than in $\overline{\mathbb{Q}} + \mathcal{L}$; part 1 derives the sharp form from it with Baker's theorem. The book introduces the strong five exponentials conjecture (p. 437) as a weaker statement than a dimension bound that includes Conjecture 11.17. The contribution of this node is the formal proof.
-- source:
--   Conjectures: M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren 326, Springer, 2000, Conjecture 11.17 (p. 399) and p. 438 (strong five exponentials, introduced on p. 437 as a weaker statement); M. Waldschmidt, On the transcendence methods of Gel'fond and Schneider in several variables, in New Advances in Transcendence Theory (Durham, 1986), Cambridge Univ. Press, 1988, 375–398, p. 377 (the strong form of the four exponentials conjecture) and p. 379 (the strong five exponentials conjecture, clearly weaker); M. Waldschmidt, Hopf algebras and transcendental numbers, in Zeta Functions, Topology and Quantum Physics, Springer, 2005, 197–219, the sharp four exponentials conjecture and Conjecture 1.5 (pp. 4–5 of the author's version). Part 1 from Conjecture 11.17 with Baker's theorem: Formal proof: Diaz modulus mission, 1 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

/-- The strong four exponentials conjecture, with Baker's theorem `hB` in its two-logarithm inhomogeneous form,
implies the sharp four exponentials conjecture (in the inline form of
`DiazModulus.diaz_of_sharp_four_exponentials`) and Waldschmidt's strong five exponentials conjecture (in the
inline form of `DiazModulus.diaz_of_strong_five_exponentials`). -/
theorem sharp_four_and_strong_five_exponentials_of_strong_four (hS : StrongFourExponentials)
    (hB : ∀ x y a b : ℂ,
          IsAlgebraic ℚ (Complex.exp x) → IsAlgebraic ℚ (Complex.exp y) →
          (∀ p q : ℚ, (p : ℂ) * x + (q : ℂ) * y = 0 → p = 0 ∧ q = 0) →
          IsAlgebraic ℚ a → IsAlgebraic ℚ b → ¬(a = 0 ∧ b = 0) →
          Transcendental ℚ (a * x + b * y)) :
    (∀ x₁ x₂ y₁ y₂ β₁₁ β₁₂ β₂₁ β₂₂ : ℂ,
        LinearIndependent ℚ ![x₁, x₂] → LinearIndependent ℚ ![y₁, y₂] →
        IsAlgebraic ℚ β₁₁ → IsAlgebraic ℚ β₁₂ → IsAlgebraic ℚ β₂₁ → IsAlgebraic ℚ β₂₂ →
        IsAlgebraic ℚ (Complex.exp (x₁ * y₁ - β₁₁)) → IsAlgebraic ℚ (Complex.exp (x₁ * y₂ - β₁₂)) →
        IsAlgebraic ℚ (Complex.exp (x₂ * y₁ - β₂₁)) → IsAlgebraic ℚ (Complex.exp (x₂ * y₂ - β₂₂)) →
        x₁ * y₁ = β₁₁ ∧ x₁ * y₂ = β₁₂ ∧ x₂ * y₁ = β₂₁ ∧ x₂ * y₂ = β₂₂) ∧
    (∀ x₁ x₂ y₁ y₂ η α₁₁ α₁₂ α₂₁ α₂₂ β : ℂ,
        LinearIndependent ℚ ![x₁, x₂] → LinearIndependent ℚ ![y₁, y₂] →
        IsAlgebraic ℚ η → η ≠ 0 →
        IsAlgebraic ℚ α₁₁ → IsAlgebraic ℚ α₁₂ → IsAlgebraic ℚ α₂₁ → IsAlgebraic ℚ α₂₂ →
        IsAlgebraic ℚ β →
        IsAlgebraic ℚ (Complex.exp (x₁ * y₁ - α₁₁)) → IsAlgebraic ℚ (Complex.exp (x₁ * y₂ - α₁₂)) →
        IsAlgebraic ℚ (Complex.exp (x₂ * y₁ - α₂₁)) → IsAlgebraic ℚ (Complex.exp (x₂ * y₂ - α₂₂)) →
        IsAlgebraic ℚ (Complex.exp (η * x₂ / x₁ - β)) →
        x₁ * y₁ = α₁₁ ∧ x₁ * y₂ = α₁₂ ∧ x₂ * y₁ = α₂₁ ∧ x₂ * y₂ = α₂₂ ∧ η * x₂ = β * x₁) := by
  sorry

end DiazModulus
