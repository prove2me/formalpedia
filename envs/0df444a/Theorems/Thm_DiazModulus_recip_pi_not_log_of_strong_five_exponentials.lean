-- Prove2me | Theorems.Thm_DiazModulus_recip_pi_not_log_of_strong_five_exponentials
-- name    : DiazModulus.recip_pi_not_log_of_strong_five_exponentials
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T11:04:19.140462+00:00
-- url     : https://prove2.me/theorems/8762030f-2925-489b-960b-d4a78d7632df
-- title:
--   Waldschmidt's strong five exponentials conjecture implies the statement (S)
-- statement:
--   **A weaker published conjecture already suffices.**
--
--   The strong five exponentials conjecture of Waldschmidt: let $x_1, x_2$ be $\mathbb{Q}$-linearly independent, let $y_1, y_2$ be $\mathbb{Q}$-linearly independent, and let $\eta$ be a non-zero algebraic number. If $\alpha_{11}, \alpha_{12}, \alpha_{21}, \alpha_{22}, \beta$ are algebraic numbers such that the five numbers
--
--   $$e^{x_iy_j - \alpha_{ij}}\ \ (i, j = 1, 2), \qquad e^{\eta x_2/x_1 - \beta}$$
--
--   are algebraic, then $x_iy_j = \alpha_{ij}$ for all $i, j$, and $\eta x_2 = \beta x_1$. It is the hypothesis `hS5`.
--
--   Waldschmidt introduced it in 1988, calling it "clearly a weaker statement than the strong four exponentials conjecture". Dropping the fifth exponential from its hypotheses gives the sharp four exponentials conjecture, which is stronger.
--
--   This node: under `hS5`, the statement (S) holds: $e^{\gamma/(i\pi)}$ is transcendental for every non-zero algebraic $\gamma$.
--
--   **Proof.** Suppose $\lambda = \gamma/(i\pi)$ has $e^{\lambda}$ algebraic. Take $x = (1, \lambda)$, $y = (1, i\pi)$, $\alpha = \begin{pmatrix} 1 & 0 \\ 0 & \gamma \end{pmatrix}$, $\eta = 1$ and $\beta = 0$. The four numbers $e^{x_iy_j-\alpha_{ij}}$ are $1, e^{i\pi} = -1, e^{\lambda}, 1$, and the fifth is $e^{\lambda}$. Hermite–Lindemann makes $\lambda$ and $i\pi$ transcendental. The conclusion $x_1y_2 = \alpha_{12}$ reads $i\pi = 0$.
--
--   This is the analogue of `DiazModulus.recip_pi_not_log_of_sfe`, with a weaker hypothesis.
--
--   **Attribution.** The conjecture is the Remark on p. 379 of M. Waldschmidt, *On the transcendence methods of Gel'fond and Schneider in several variables*, in *New Advances in Transcendence Theory* (Durham 1986), Cambridge 1988. It is also Conjecture 1.5 ("sharp five exponentials") of his *Hopf algebras and transcendental numbers* (2005) and appears on p. 438 of his *Diophantine Approximation on Linear Algebraic Groups* (2000).
-- source:
--   Conjecture: M. Waldschmidt, On the transcendence methods of Gel'fond and Schneider in several variables, in New Advances in Transcendence Theory (Durham, 1986), Cambridge Univ. Press, 1988, 375–398, p. 379; M. Waldschmidt, Hopf algebras and transcendental numbers, in Zeta Functions, Topology and Quantum Physics, Springer, 2005, Conjecture 1.5; M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren 326, Springer, 2000, p. 438. Instantiation and formal proof: Diaz modulus mission, 24 September 2026 (C. Perassi). Hermite-Lindemann discharged from DiazModulus.hermite_lindemann_holds.

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem recip_pi_not_log_of_strong_five_exponentials (hS5 : ∀ x₁ x₂ y₁ y₂ η α₁₁ α₁₂ α₂₁ α₂₂ β : ℂ,
      LinearIndependent ℚ ![x₁, x₂] → LinearIndependent ℚ ![y₁, y₂] →
      IsAlgebraic ℚ η → η ≠ 0 →
      IsAlgebraic ℚ α₁₁ → IsAlgebraic ℚ α₁₂ → IsAlgebraic ℚ α₂₁ → IsAlgebraic ℚ α₂₂ →
      IsAlgebraic ℚ β →
      IsAlgebraic ℚ (Complex.exp (x₁ * y₁ - α₁₁)) → IsAlgebraic ℚ (Complex.exp (x₁ * y₂ - α₁₂)) →
      IsAlgebraic ℚ (Complex.exp (x₂ * y₁ - α₂₁)) → IsAlgebraic ℚ (Complex.exp (x₂ * y₂ - α₂₂)) →
      IsAlgebraic ℚ (Complex.exp (η * x₂ / x₁ - β)) →
      x₁ * y₁ = α₁₁ ∧ x₁ * y₂ = α₁₂ ∧ x₂ * y₁ = α₂₁ ∧ x₂ * y₂ = α₂₂ ∧ η * x₂ = β * x₁) :
    ∀ γ : ℂ, IsAlgebraic ℚ γ → γ ≠ 0 →
      ¬ IsAlgebraic ℚ (Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I))) := by
  sorry

end DiazModulus
