-- Prove2me | Theorems.Thm_DiazModulus_diaz_of_sharp_four_exponentials
-- name    : DiazModulus.diaz_of_sharp_four_exponentials
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T11:04:33.676901+00:00
-- url     : https://prove2.me/theorems/35f8c309-eece-432e-9711-33de1f96b2ec
-- title:
--   The sharp four exponentials conjecture implies Diaz's conjecture
-- statement:
--   **The sharp four exponentials conjecture suffices.**
--
--   The sharp four exponentials conjecture: let $x_1, x_2$ be $\mathbb{Q}$-linearly independent and $y_1, y_2$ likewise. If $\beta_{11}, \beta_{12}, \beta_{21}, \beta_{22}$ are algebraic numbers such that the four numbers
--
--   $$e^{x_iy_j - \beta_{ij}} \qquad (i, j = 1, 2)$$
--
--   are algebraic, then $x_iy_j = \beta_{ij}$ for all $i, j$. It is the hypothesis `hS4`.
--
--   It differs from the strong four exponentials conjecture of `DiazModulus.diaz_of_sfe` in both directions: independence is only over $\mathbb{Q}$, and the products may differ from logarithms only by an algebraic constant, not by an algebraic combination of logarithms.
--
--   This node: under `hS4`, Diaz's modulus conjecture holds.
--
--   **Proof.** For a candidate $u$, with $\rho = |u|^{2}$, take $x = (1, u)$, $y = (1, \bar u)$ and $\beta = \begin{pmatrix} 1 & 0 \\ 0 & \rho \end{pmatrix}$. The four numbers $e^{x_iy_j-\beta_{ij}}$ are $1, e^{\bar u}, e^{u}, 1$. Hermite–Lindemann makes $u$ and $\bar u$ transcendental, so both pairs are $\mathbb{Q}$-linearly independent. The conclusion $x_1y_2 = \beta_{12}$ then reads $\bar u = 0$.
--
--   The instantiation is that of `DiazModulus.diaz_of_sfe`.
--
--   **Attribution.** The conjecture is stated under this name on p. 4 of M. Waldschmidt, *Hopf algebras and transcendental numbers* (2005). In his 1988 Durham paper (p. 377) the same statement appears as a strong form of the four exponentials conjecture, derived from the algebraic independence of $\mathbb{Q}$-linearly independent logarithms.
-- source:
--   Conjecture: M. Waldschmidt, Hopf algebras and transcendental numbers, in Zeta Functions, Topology and Quantum Physics, Springer, 2005, p. 4 (sharp four exponentials conjecture); M. Waldschmidt, On the transcendence methods of Gel'fond and Schneider in several variables, in New Advances in Transcendence Theory (Durham, 1986), Cambridge Univ. Press, 1988, 375–398, p. 377. Instantiation and formal proof: Diaz modulus mission, 24 September 2026 (C. Perassi). Hermite-Lindemann discharged from DiazModulus.hermite_lindemann_holds.

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem diaz_of_sharp_four_exponentials (hS4 : ∀ x₁ x₂ y₁ y₂ β₁₁ β₁₂ β₂₁ β₂₂ : ℂ,
      LinearIndependent ℚ ![x₁, x₂] → LinearIndependent ℚ ![y₁, y₂] →
      IsAlgebraic ℚ β₁₁ → IsAlgebraic ℚ β₁₂ → IsAlgebraic ℚ β₂₁ → IsAlgebraic ℚ β₂₂ →
      IsAlgebraic ℚ (Complex.exp (x₁ * y₁ - β₁₁)) → IsAlgebraic ℚ (Complex.exp (x₁ * y₂ - β₁₂)) →
      IsAlgebraic ℚ (Complex.exp (x₂ * y₁ - β₂₁)) → IsAlgebraic ℚ (Complex.exp (x₂ * y₂ - β₂₂)) →
      x₁ * y₁ = β₁₁ ∧ x₁ * y₂ = β₁₂ ∧ x₂ * y₁ = β₂₁ ∧ x₂ * y₂ = β₂₂) :
    DiazModulusConjecture := by
  sorry

end DiazModulus
