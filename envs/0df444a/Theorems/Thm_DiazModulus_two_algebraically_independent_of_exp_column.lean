-- Prove2me | Theorems.Thm_DiazModulus_two_algebraically_independent_of_exp_column
-- name    : DiazModulus.two_algebraically_independent_of_exp_column
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-30T07:39:09.425542+00:00
-- url     : https://prove2.me/theorems/b3e7e62f-38e7-469f-9b86-446206bec1a3
-- title:
--   Waldschmidt 1973: if one column of the four exponentials is algebraic, two of the eight numbers are algebraically independent
-- statement:
--   Let $x_1, x_2$ be complex numbers linearly independent over $\mathbb{Q}$, and $y_1, y_2$ complex numbers linearly independent over $\mathbb{Q}$. If $e^{x_1y_2}$ and $e^{x_2y_2}$ are algebraic, then two of the eight numbers
--
--   $$x_1,\ x_2,\ y_1,\ y_2,\ e^{x_1y_1},\ e^{x_1y_2},\ e^{x_2y_1},\ e^{x_2y_2}$$
--
--   are algebraically independent over $\mathbb{Q}$.
--
--   **Proof.** Suppose not. One of $x_1, y_2$ is transcendental by Hermite–Lindemann, since $x_1y_2 \neq 0$ and $e^{x_1y_2}$ is algebraic. The pair lemma `Transcendence.isAlgebraic_adjoin_of_not_algebraicIndependent_pair` then puts all eight numbers in the algebraic closure of $\mathbb{Q}[t]$ for that transcendental $t$, so they generate a field of transcendence degree at most one. The column construction (`FourExp.small_polynomials_of_column`, after Waldschmidt's Lemmes 4–7) then produces integer polynomials that are too small at a transcendental point, and Gel'fond's criterion in Waldschmidt's 1971 form (`FourExp.transcendence_criterion`) makes that point algebraic, a contradiction.
--
--   The two algebraic exponentials must share a column. The transcendental ones, $e^{x_1y_1}$ and $e^{x_2y_1}$, are sampled only along the short side of the interpolation grid, where their powers cost degree in the transcendental generator and not height. The four exponentials theorem in transcendence degree one (`DiazModulus.four_exponentials_trdeg_one`) is the case in which all four exponentials are algebraic.
--
--   **Novelty.** None: this is the Théorème of Waldschmidt (1973), p. 192, restated as Theorem 7.4.1 of *Nombres transcendants* (1974), Corollary 15.28(c) of *Diophantine Approximation on Linear Algebraic Groups* (2000) and Corollary 1.2(c) of Roy–Waldschmidt (1997). The paper's note added in proof (p. 202) records that W. D. Brownawell found these results independently. The contribution of this node is the formal proof.
-- source:
--   M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973), 191–202, Théorème (p. 192). Found independently by W. D. Brownawell, The algebraic independence of certain numbers related to the exponential function, J. Number Theory 6 (1974), 22–31 (see the paper's note added in proof, p. 202). Formal proof: Diaz modulus mission, 30 September 2026 (C. Perassi).

import Mathlib

namespace DiazModulus

/-- **Waldschmidt's theorem of 1973.** Let `x₁, x₂` be `ℚ`-linearly independent complex numbers,
`y₁, y₂` also, and suppose that `e^{x₁y₂}` and `e^{x₂y₂}` are algebraic. Then two of the eight
numbers `xᵢ`, `yⱼ`, `e^{xᵢyⱼ}` are algebraically independent over `ℚ`.

M. Waldschmidt, *Solution du huitième problème de Schneider*, J. Number Theory 5 (1973), 191–202,
Théorème (p. 192); also Theorem 7.4.1 of *Nombres transcendants* (LN 402), Corollary 15.28(c) of
*Diophantine Approximation on Linear Algebraic Groups*, and Corollary 1.2(c) of Roy–Waldschmidt
(1997). The statement is exactly the hypothesis `hW73` of
`DiazModulus.pi_e_exp_pi_sq_indep_of_exp_i_rat_div_pi`. -/
theorem two_algebraically_independent_of_exp_column :
    ∀ x₁ x₂ y₁ y₂ : ℂ, LinearIndependent ℚ ![x₁, x₂] → LinearIndependent ℚ ![y₁, y₂] →
      IsAlgebraic ℚ (Complex.exp (x₁ * y₂)) → IsAlgebraic ℚ (Complex.exp (x₂ * y₂)) →
      ∃ a ∈ ({x₁, x₂, y₁, y₂, Complex.exp (x₁ * y₁), Complex.exp (x₁ * y₂),
          Complex.exp (x₂ * y₁), Complex.exp (x₂ * y₂)} : Set ℂ),
        ∃ b ∈ ({x₁, x₂, y₁, y₂, Complex.exp (x₁ * y₁), Complex.exp (x₁ * y₂),
            Complex.exp (x₂ * y₁), Complex.exp (x₂ * y₂)} : Set ℂ),
          AlgebraicIndependent ℚ ![a, b] := by
  sorry

end DiazModulus
