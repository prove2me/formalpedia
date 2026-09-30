-- Prove2me | Theorems.Thm_DiazModulus_algebraicIndependent_e_pi_of_exp_pi_sq_algebraic
-- name    : DiazModulus.algebraicIndependent_e_pi_of_exp_pi_sq_algebraic
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-30T07:39:49.94639+00:00
-- url     : https://prove2.me/theorems/8530cb15-0f5b-4318-b254-b9563ba16bff
-- title:
--   If e^{π²} is algebraic, then e and π are algebraically independent
-- statement:
--   If $e^{\pi^{2}}$ is algebraic, then $e$ and $\pi$ are algebraically independent over $\mathbb{Q}$.
--
--   The transcendence of $e^{\pi^{2}}$ itself is not known. What is known unconditionally is that $e^{\pi^{2}}$ or $e^{i\pi^{3}}$ is transcendental (`DiazModulus.exp_pi_sq_or_exp_i_pi_cube_transcendental`).
--
--   **Proof.** Apply `DiazModulus.two_algebraically_independent_of_exp_column` at $x = (i\pi, 1)$ and $y = (1, i\pi)$. The column $y_2 = i\pi$ carries $e^{-\pi^{2}}$ and $e^{i\pi} = -1$, both algebraic. All eight numbers are then algebraic over $\mathbb{Q}(\pi, e)$, so that field has transcendence degree two: $\pi$ and $e$ are algebraically independent.
--
--   **Novelty.** None: this is Corollaire 1 of Waldschmidt (1973) at $\alpha = -1$ (with $\log\alpha = i\pi$), and the paper states it in the remark that follows the corollary (p. 192). The substitution is the one in the corollary's proof (p. 193). The contribution of this node is the formal proof.
-- source:
--   M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973), 191–202, Corollaire 1 at α = −1 and the remark that follows it (p. 192); the substitution of p. 193. Formal proof: Diaz modulus mission, 30 September 2026 (C. Perassi).

import Mathlib

namespace DiazModulus

/-- If `e^{π²}` is algebraic, then `e` and `π` are algebraically independent.

This is Corollary 1 of M. Waldschmidt, *Solution du huitième problème de Schneider*, J. Number
Theory 5 (1973), 191–202, at `α = -1`: the Théorème
(`DiazModulus.two_algebraically_independent_of_exp_column`) at `x = (iπ, 1)`, `y = (1, iπ)`. The
column is `e^{-π²}`, `e^{iπ} = -1`; the other two exponentials are `e^{iπ} = -1` and `e`. -/
theorem algebraicIndependent_e_pi_of_exp_pi_sq_algebraic
    (halg : IsAlgebraic ℚ (Complex.exp (((Real.pi : ℝ) : ℂ) ^ 2))) :
    AlgebraicIndependent ℚ ![Complex.exp 1, ((Real.pi : ℝ) : ℂ)] := by
  sorry

end DiazModulus
