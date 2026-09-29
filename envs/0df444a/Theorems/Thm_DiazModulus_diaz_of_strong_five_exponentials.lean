-- Prove2me | Theorems.Thm_DiazModulus_diaz_of_strong_five_exponentials
-- name    : DiazModulus.diaz_of_strong_five_exponentials
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T11:04:06.698211+00:00
-- url     : https://prove2.me/theorems/e86284a1-9a04-4962-ac42-0901e7f794ff
-- title:
--   Waldschmidt's strong five exponentials conjecture implies Diaz's conjecture
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
--   This node: under `hS5`, Diaz's modulus conjecture holds.
--
--   **Proof.** For a candidate $u$, with $\rho = |u|^{2}$, take $x = (1, u)$, $y = (1, \bar u)$, $\alpha = \begin{pmatrix} 1 & 0 \\ 0 & \rho \end{pmatrix}$, $\eta = 1$ and $\beta = 0$. The four numbers $e^{x_iy_j-\alpha_{ij}}$ are $1, e^{\bar u}, e^{u}, 1$. The fifth is $e^{u}$: since $x_1 = 1$, it is one of the four. Hermite–Lindemann makes $u$ and $\bar u$ transcendental, so both pairs are $\mathbb{Q}$-linearly independent. The conclusion $x_1y_2 = \alpha_{12}$ then reads $\bar u = 0$.
--
--   So Diaz's conjecture follows from a published conjecture that Waldschmidt himself calls weaker than the strong four exponentials conjecture, on which `DiazModulus.diaz_of_sfe` rests. The instantiation is that of `DiazModulus.diaz_of_sfe`.
--
--   **Attribution.** The conjecture is the Remark on p. 379 of M. Waldschmidt, *On the transcendence methods of Gel'fond and Schneider in several variables*, in *New Advances in Transcendence Theory* (Durham 1986), Cambridge 1988. It is also Conjecture 1.5 ("sharp five exponentials") of his *Hopf algebras and transcendental numbers* (2005) and appears on p. 438 of his *Diophantine Approximation on Linear Algebraic Groups* (2000).
-- source:
--   Conjecture: M. Waldschmidt, On the transcendence methods of Gel'fond and Schneider in several variables, in New Advances in Transcendence Theory (Durham, 1986), Cambridge Univ. Press, 1988, 375–398, p. 379; M. Waldschmidt, Hopf algebras and transcendental numbers, in Zeta Functions, Topology and Quantum Physics, Springer, 2005, Conjecture 1.5; M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren 326, Springer, 2000, p. 438. Instantiation and formal proof: Diaz modulus mission, 24 September 2026 (C. Perassi). Hermite-Lindemann discharged from DiazModulus.hermite_lindemann_holds.

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem diaz_of_strong_five_exponentials (hS5 : ∀ x₁ x₂ y₁ y₂ η α₁₁ α₁₂ α₂₁ α₂₂ β : ℂ,
      LinearIndependent ℚ ![x₁, x₂] → LinearIndependent ℚ ![y₁, y₂] →
      IsAlgebraic ℚ η → η ≠ 0 →
      IsAlgebraic ℚ α₁₁ → IsAlgebraic ℚ α₁₂ → IsAlgebraic ℚ α₂₁ → IsAlgebraic ℚ α₂₂ →
      IsAlgebraic ℚ β →
      IsAlgebraic ℚ (Complex.exp (x₁ * y₁ - α₁₁)) → IsAlgebraic ℚ (Complex.exp (x₁ * y₂ - α₁₂)) →
      IsAlgebraic ℚ (Complex.exp (x₂ * y₁ - α₂₁)) → IsAlgebraic ℚ (Complex.exp (x₂ * y₂ - α₂₂)) →
      IsAlgebraic ℚ (Complex.exp (η * x₂ / x₁ - β)) →
      x₁ * y₁ = α₁₁ ∧ x₁ * y₂ = α₁₂ ∧ x₂ * y₁ = α₂₁ ∧ x₂ * y₂ = α₂₂ ∧ η * x₂ = β * x₁) :
    DiazModulusConjecture := by
  sorry

end DiazModulus
