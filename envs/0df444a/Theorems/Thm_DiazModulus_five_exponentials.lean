-- Prove2me | Theorems.Thm_DiazModulus_five_exponentials
-- name    : DiazModulus.five_exponentials
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-01T09:19:09.363057+00:00
-- url     : https://prove2.me/theorems/ba534ec4-c268-4fce-b998-3820dd0732ff
-- title:
--   The five exponentials theorem: for ℚ-independent x₀, x₁ and y₀, y₁ and algebraic η ≠ 0, one of the e^{xᵢyⱼ} and e^{ηx₁/x₀} is transcendental
-- statement:
--   **The five exponentials theorem.**
--
--   Let $x_0, x_1 \in \mathbb{C}$ be linearly independent over $\mathbb{Q}$, let $y_0, y_1 \in \mathbb{C}$ be linearly independent over $\mathbb{Q}$, and let $\eta$ be a non-zero algebraic number. Then at least one of the five numbers
--
--   $$e^{x_0y_0}, \qquad e^{x_0y_1}, \qquad e^{x_1y_0}, \qquad e^{x_1y_1}, \qquad e^{\eta x_1/x_0}$$
--
--   is transcendental. ($x_0 \neq 0$ by independence, so the quotient is defined.)
--
--   The sources number from $1$: the fifth number is $e^{\eta x_2/x_1}$ in Waldschmidt (1988, Cor. 2.2) and $e^{\gamma x_1/x_2}$ in DALAG (§11.3.3, Example 1), the same statement after exchanging $x_1$ and $x_2$. Here $\mathcal{L}$ is the set of logarithms of algebraic numbers (the $z \in \mathbb{C}$ with $e^z$ algebraic), and $\widetilde{\mathcal{L}}$ is the $\overline{\mathbb{Q}}$-vector space spanned by $1$ and $\mathcal{L}$, with $\overline{\mathbb{Q}}$ the field of algebraic numbers.
--
--   **Proof.** Suppose the five numbers are algebraic, and put $y_2 = \eta/x_0$. (1) $x$ is linearly independent over $\overline{\mathbb{Q}}$: $x_0y_0$ and $x_1y_0$ are logarithms of algebraic numbers, linearly independent over $\mathbb{Q}$ since $y_0 \neq 0$; a relation $g_0x_0 + g_1x_1 = 0$ with $g_i \in \overline{\mathbb{Q}}$ gives $g_0(x_0y_0) + g_1(x_1y_0) = 0$, and Baker's theorem (`Schanuel.baker_linear_forms_in_logarithms`, with no constant term) gives $g = 0$. (2) $(y_0, y_1, y_2)$ is linearly independent over $\overline{\mathbb{Q}}$: a relation $g_0y_0 + g_1y_1 + g_2y_2 = 0$, multiplied by $x_0$, reads $g_2\eta + g_0(x_0y_0) + g_1(x_0y_1) = 0$, where $x_0y_0, x_0y_1$ are $\mathbb{Q}$-independent logarithms; Baker's theorem with the constant term $g_2\eta$ gives $g = 0$, as $\eta \neq 0$. (3) The six products $x_iy_j$ lie in $\widetilde{\mathcal{L}}$: four are logarithms by hypothesis, $x_0y_2 = \eta \in \overline{\mathbb{Q}}$, and $x_1y_2 = \eta x_1/x_0$ is a logarithm by hypothesis. Roy's strong six exponentials theorem (`DiazModulus.strong_six_exponentials_unconditional`) says that (1)–(3) cannot hold together. This is the derivation of DALAG's Remark after Cor. 11.16 (p. 399): Baker's theorem turns $\mathbb{Q}$-linear independence into $\overline{\mathbb{Q}}$-linear independence.
--
--   **Novelty.** None: this is the five exponentials theorem of Waldschmidt (1988, Cor. 2.2, p. 378), also DALAG §11.3.3, Example 1, p. 385. The derivation from Roy's strong six exponentials theorem (Roy 1992, Cor. 2; DALAG Cor. 11.16) and Baker's theorem is DALAG's Remark after Cor. 11.16, p. 399. The contribution of this node is the formal proof.
-- source:
--   Known: M. Waldschmidt, On the transcendence methods of Gel'fond and Schneider in several variables, in New Advances in Transcendence Theory (Durham, 1986), Cambridge Univ. Press, 1988, 375–398, Cor. 2.2, p. 378; M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, §11.3.3, Example 1, p. 385. Proof as in DALAG, Remark after Cor. 11.16, p. 399, from Roy's strong six exponentials theorem (D. Roy, Matrices whose coefficients are linear forms in logarithms, J. Number Theory 41 (1992), 22–47, Cor. 2; DALAG Cor. 11.16) and Baker's theorem (A. Baker, Linear forms in the logarithms of algebraic numbers I, Mathematika 13 (1966), 204–216). Uses Schanuel.baker_linear_forms_in_logarithms and DiazModulus.strong_six_exponentials_unconditional. C2 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 30 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

/-- **The five exponentials theorem** (M. Waldschmidt, *On the transcendence methods of Gel'fond
and Schneider in several variables*, New Advances in Transcendence Theory (Durham 1986), 1988,
Cor. 2.2, p. 378; DALAG § 11.3.3, Example 1, p. 385).

Let `x₁, x₂` be `ℚ`-linearly independent, `y₁, y₂` be `ℚ`-linearly independent, and `η` a nonzero
algebraic number. Then at least one of the five numbers
`e^{x₁y₁}, e^{x₁y₂}, e^{x₂y₁}, e^{x₂y₂}, e^{η x₂ / x₁}` is transcendental.

(`x₁ ≠ 0` follows from the independence of `x`, so the quotient is well defined.) -/
theorem five_exponentials :
    ∀ x y : Fin 2 → ℂ, ∀ η : ℂ, LinearIndependent ℚ x → LinearIndependent ℚ y →
      IsAlgebraic ℚ η → η ≠ 0 →
      ¬ ((∀ i j, IsAlgebraic ℚ (Complex.exp (x i * y j))) ∧
          IsAlgebraic ℚ (Complex.exp (η * x 1 / x 0))) := by
  sorry

end DiazModulus
