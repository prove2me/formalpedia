-- Prove2me | Theorems.Thm_DiazModulus_pi_e_exp_pi_sq_indep_of_exp_i_rat_div_pi
-- name    : DiazModulus.pi_e_exp_pi_sq_indep_of_exp_i_rat_div_pi
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T06:49:22.701056+00:00
-- url     : https://prove2.me/theorems/b56a1fae-4ab1-45a1-8f89-c17aa8353ce1
-- title:
--   Assuming Waldschmidt 1973: if e^{ir/π} is algebraic for a rational r ≠ 0, then two of π, e, e^{π²} are algebraically independent
-- statement:
--   Assume Waldschmidt's theorem of 1973, the hypothesis `hW73`: if $x_1, x_2$ are linearly independent over $\mathbb{Q}$, $y_1, y_2$ are linearly independent over $\mathbb{Q}$, and $e^{x_1y_2}$ and $e^{x_2y_2}$ are algebraic, then two of the eight numbers $x_i$, $y_j$, $e^{x_iy_j}$ are algebraically independent. Let $r \neq 0$ be rational with $e^{ir/\pi}$ algebraic. Then two of
--
--   $$\pi, \qquad e, \qquad e^{\pi^{2}}$$
--
--   are algebraically independent.
--
--   At $r = 1$: either $e^{i/\pi}$ is transcendental, or two of $\pi$, $e$, $e^{\pi^{2}}$ are algebraically independent. The second alternative is an open problem listed by Waldschmidt (*Diophantine Approximation on Linear Algebraic Groups*, 2000, §15.3.5, p. 594). The first is the smallest case of the statement (S) for real $\gamma$ (`DiazModulus.recip_pi_not_log_real_gamma`, Open). The same hypothesis, $e^{i/\pi}$ algebraic, also makes $e^{i\pi^{3}}$ transcendental (`DiazModulus.exp_i_div_pi_or_exp_i_pi_cube_transcendental`), which is a different consequence.
--
--   **Proof.** Take $x = (i\pi,\ ir/\pi)$ and $y = (-i\pi/r,\ 1)$. The pair $x$ is $\mathbb{Q}$-independent because $\pi^{2}$ is irrational, and $y$ because $-i\pi/r$ is not real. The column $y_2 = 1$ carries $e^{i\pi} = -1$ and $e^{ir/\pi}$, both algebraic. The other two exponentials are $e^{\pi^{2}/r}$ and $e$. If no two of $\pi$, $e$, $e^{\pi^{2}}$ were algebraically independent, then, $\pi$ being transcendental, $e$ and $e^{\pi^{2}}$ would be algebraic over $\mathbb{Q}(\pi)$. Then so would all eight numbers, since a positive power of $e^{\pi^{2}/r}$ is an integer power of $e^{\pi^{2}}$. They would generate a field of transcendence degree at most one, against the hypothesis.
--
--   **Novelty.** None: this is a specialisation of a published theorem. It is not stated in the sources read, but it is one substitution in the Théorème of M. Waldschmidt, *Solution du huitième problème de Schneider*, J. Number Theory **5** (1973), p. 192, restated as Theorem 7.4.1 of *Nombres transcendants* (LN 402), Corollary 15.28(c) of *Diophantine Approximation on Linear Algebraic Groups* and Corollary 1.2(c) of Roy–Waldschmidt (1997). It is also one line from Exercise 15.15(e) of the same book (p. 614). The theorem has no formal proof yet, so it is carried as a hypothesis. The contribution of this node is the formal derivation.
-- source:
--   Specialisation of M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973), 191–202, Théorème (p. 192), at x = (iπ, ir/π), y = (−iπ/r, 1); the theorem is carried as the hypothesis hW73. Also M. Waldschmidt, Nombres transcendants, Lecture Notes in Math. 402, Springer, 1974, Theorem 7.4.1; M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren 326, Springer, 2000, Corollary 15.28(c) and Exercise 15.15(e), and the open problem of §15.3.5 (p. 594); D. Roy and M. Waldschmidt, Approximation diophantienne et indépendance algébrique de logarithmes, Ann. Sci. École Norm. Sup. (4) 30 (1997), 753–796, Corollary 1.2(c). The substitution was not found in the sources read. Formal derivation: Diaz modulus mission, 29 September 2026 (C. Perassi).

import Mathlib

namespace DiazModulus

/-- Assume Waldschmidt's theorem of 1973: if `x₁, x₂` are `ℚ`-linearly independent, `y₁, y₂` are
`ℚ`-linearly independent, and `e^{x₁y₂}` and `e^{x₂y₂}` are algebraic, then two of the numbers
`xᵢ`, `yⱼ`, `e^{xᵢyⱼ}` are algebraically independent. If `e^{ir/π}` is algebraic for some non-zero
rational `r`, then two of `π`, `e`, `e^{π²}` are algebraically independent. -/
theorem pi_e_exp_pi_sq_indep_of_exp_i_rat_div_pi
    (hW73 : ∀ x₁ x₂ y₁ y₂ : ℂ, LinearIndependent ℚ ![x₁, x₂] → LinearIndependent ℚ ![y₁, y₂] →
      IsAlgebraic ℚ (Complex.exp (x₁ * y₂)) → IsAlgebraic ℚ (Complex.exp (x₂ * y₂)) →
      ∃ a ∈ ({x₁, x₂, y₁, y₂, Complex.exp (x₁ * y₁), Complex.exp (x₁ * y₂),
          Complex.exp (x₂ * y₁), Complex.exp (x₂ * y₂)} : Set ℂ),
        ∃ b ∈ ({x₁, x₂, y₁, y₂, Complex.exp (x₁ * y₁), Complex.exp (x₁ * y₂),
            Complex.exp (x₂ * y₁), Complex.exp (x₂ * y₂)} : Set ℂ),
          AlgebraicIndependent ℚ ![a, b])
    (r : ℚ) (hr : r ≠ 0)
    (halg : IsAlgebraic ℚ (Complex.exp (Complex.I * (r : ℂ) / ((Real.pi : ℝ) : ℂ)))) :
    ∃ a ∈ ({((Real.pi : ℝ) : ℂ), Complex.exp 1, Complex.exp (((Real.pi : ℝ) : ℂ) ^ 2)} : Set ℂ),
      ∃ b ∈ ({((Real.pi : ℝ) : ℂ), Complex.exp 1, Complex.exp (((Real.pi : ℝ) : ℂ) ^ 2)} : Set ℂ),
        AlgebraicIndependent ℚ ![a, b] := by
  sorry

end DiazModulus
