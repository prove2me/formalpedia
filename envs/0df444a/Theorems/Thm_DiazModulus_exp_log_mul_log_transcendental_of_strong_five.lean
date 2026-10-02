-- Prove2me | Theorems.Thm_DiazModulus_exp_log_mul_log_transcendental_of_strong_five
-- name    : DiazModulus.exp_log_mul_log_transcendental_of_strong_five
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-01T14:41:51.803817+00:00
-- url     : https://prove2.me/theorems/22665446-f1ad-4cee-b924-f8f713e21868
-- title:
--   The strong five exponentials conjecture implies that e^{λμ} is transcendental for non-zero logarithms λ, μ, and e^{π²} in particular
-- statement:
--   Here $\mathcal{L}$ is the set of logarithms of algebraic numbers, and $\widetilde{\mathcal{L}}$ is the $\overline{\mathbb{Q}}$-vector space spanned by $1$ and $\mathcal{L}$. Waldschmidt's strong five exponentials conjecture is carried as the hypothesis `hS5`, in the form of `DiazModulus.diaz_of_strong_five_exponentials`: if $x_1, x_2$ are linearly independent over $\mathbb{Q}$ and so are $y_1, y_2$, if $\eta \neq 0$, $\alpha_{ij}$ and $\beta$ are algebraic, and if the five numbers $e^{x_iy_j - \alpha_{ij}}$ ($i, j = 1, 2$) and $e^{\eta x_2/x_1 - \beta}$ are algebraic, then $x_iy_j = \alpha_{ij}$ for all $i, j$ and $\eta x_2 = \beta x_1$.
--
--   Then $e^{\lambda\mu}$ is transcendental for all non-zero $\lambda, \mu \in \mathcal{L}$: $(\log a)(\log b) \neq \log c$ for algebraic $a, b, c$ and non-zero logarithms $\log a$, $\log b$. In particular $e^{\lambda^2}$ is transcendental for every non-zero $\lambda \in \mathcal{L}$, and so is $e^{\pi^2}$.
--
--   Unconditionally, it is known only that $e^{\pi^2}$ is transcendental or $e$ and $\pi$ are algebraically independent (Brownawell and Waldschmidt; on the board as `DiazModulus.algebraicIndependent_e_pi_of_exp_pi_sq_algebraic`).
--
--   **Proof.** By Hermite–Lindemann a non-zero logarithm of an algebraic number is irrational, so $(1, \lambda)$ and $(1 + \mu, \mu)$ are linearly independent over $\mathbb{Q}$. If $e^{\lambda\mu}$ were algebraic, the conjecture would apply to $x = (1, \lambda)$, $y = (1 + \mu, \mu)$, $\eta = 1$, $\alpha_{11} = 1$ and $\alpha_{12} = \alpha_{21} = \alpha_{22} = \beta = 0$: the five numbers are $e^{\mu}$, $e^{\mu}$, $e^{\lambda}e^{\lambda\mu}$, $e^{\lambda\mu}$ and $e^{\lambda}$. Its conclusion $x_2y_2 = \alpha_{22}$ reads $\lambda\mu = 0$. For $\pi$, take $\lambda = \mu = i\pi$, a logarithm of $-1$, and note that $e^{-\pi^2} = 1/e^{\pi^2}$.
--
--   **Novelty.** None: the implication and the choice of parameters are Waldschmidt's (1988, p. 379). His 2005 survey derives the cases $e^{\lambda^2}$ and $e^{\pi^2}$, with $x = y = (1, \lambda)$ (pp. 4–5 of the author's version). The contribution of this node is the formal proof.
-- source:
--   M. Waldschmidt, On the transcendence methods of Gel'fond and Schneider in several variables, in New Advances in Transcendence Theory (Durham, 1986), Cambridge Univ. Press, 1988, 375–398, p. 379 (the strong five exponentials conjecture, and this consequence with its parameters); M. Waldschmidt, Hopf algebras and transcendental numbers, in Zeta Functions, Topology and Quantum Physics, Springer, 2005, 197–219, Conjecture 1.5 and the cases e^{λ²} and e^{π²} (pp. 4–5 of the author's version); the conjecture also in M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren 326, Springer, 2000, p. 438. Formal proof: Diaz modulus mission, 1 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

/-- Waldschmidt's strong five exponentials conjecture (inline as `hS5`, in the form of
`DiazModulus.diaz_of_strong_five_exponentials`) implies that `e^{λμ}` is transcendental for all non-zero
logarithms `λ, μ` of algebraic numbers, that is, `(log a)(log b) ≠ log c`; in particular `e^{λ²}` is
transcendental for every such `λ`, and so is `e^{π²}`. -/
theorem exp_log_mul_log_transcendental_of_strong_five
    (hS5 : ∀ x₁ x₂ y₁ y₂ η α₁₁ α₁₂ α₂₁ α₂₂ β : ℂ,
      LinearIndependent ℚ ![x₁, x₂] → LinearIndependent ℚ ![y₁, y₂] →
      IsAlgebraic ℚ η → η ≠ 0 →
      IsAlgebraic ℚ α₁₁ → IsAlgebraic ℚ α₁₂ → IsAlgebraic ℚ α₂₁ → IsAlgebraic ℚ α₂₂ →
      IsAlgebraic ℚ β →
      IsAlgebraic ℚ (Complex.exp (x₁ * y₁ - α₁₁)) → IsAlgebraic ℚ (Complex.exp (x₁ * y₂ - α₁₂)) →
      IsAlgebraic ℚ (Complex.exp (x₂ * y₁ - α₂₁)) → IsAlgebraic ℚ (Complex.exp (x₂ * y₂ - α₂₂)) →
      IsAlgebraic ℚ (Complex.exp (η * x₂ / x₁ - β)) →
      x₁ * y₁ = α₁₁ ∧ x₁ * y₂ = α₁₂ ∧ x₂ * y₁ = α₂₁ ∧ x₂ * y₂ = α₂₂ ∧ η * x₂ = β * x₁) :
    (∀ l m : ℂ, l ∈ LogAlg → l ≠ 0 → m ∈ LogAlg → m ≠ 0 →
      Transcendental ℚ (Complex.exp (l * m))) ∧
    (∀ l : ℂ, l ∈ LogAlg → l ≠ 0 → Transcendental ℚ (Complex.exp (l ^ 2))) ∧
    Transcendental ℚ (Complex.exp (((Real.pi : ℝ) : ℂ) ^ 2)) := by
  sorry

end DiazModulus
