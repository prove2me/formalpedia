-- Prove2me | Theorems.Thm_DiazModulus_pi_e_exp_pi_sq_indep_of_exp_i_rat_div_pi_algebraic
-- name    : DiazModulus.pi_e_exp_pi_sq_indep_of_exp_i_rat_div_pi_algebraic
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-30T07:39:23.053291+00:00
-- url     : https://prove2.me/theorems/662e4d8c-f618-49eb-9562-8a42f76b9560
-- title:
--   If e^{ir/π} is algebraic for a rational r ≠ 0, then two of π, e, e^{π²} are algebraically independent
-- statement:
--   Let $r \neq 0$ be rational. If $e^{ir/\pi}$ is algebraic, then two of
--
--   $$\pi, \qquad e, \qquad e^{\pi^{2}}$$
--
--   are algebraically independent.
--
--   At $r = 1$: either $e^{i/\pi}$, the smallest case of the statement (S) for real $\gamma$ (`DiazModulus.recip_pi_not_log_real_gamma`, Open), is transcendental, or two of $\pi$, $e$, $e^{\pi^{2}}$ are algebraically independent, an open problem listed in Waldschmidt's *Diophantine Approximation on Linear Algebraic Groups* (2000), §15.3.5.
--
--   **Proof.** `DiazModulus.pi_e_exp_pi_sq_indep_of_exp_i_rat_div_pi` proves this with Waldschmidt's 1973 Théorème as a hypothesis, and `DiazModulus.two_algebraically_independent_of_exp_column` proves the Théorème.
--
--   **Novelty.** None: this is a specialisation of a published theorem, at $x = (i\pi,\ ir/\pi)$ and $y = (-i\pi/r,\ 1)$. It is one line from Exercise 15.15(e) of *Diophantine Approximation on Linear Algebraic Groups*. The substitution itself was not found in the sources read.
-- source:
--   Specialisation of M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973), 191–202, Théorème (p. 192), at x = (iπ, ir/π), y = (−iπ/r, 1); compare M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren 326, Springer, 2000, Exercise 15.15(e) and §15.3.5. Formal proof: Diaz modulus mission, 30 September 2026 (C. Perassi).

import Mathlib

namespace DiazModulus

/-- If `e^{ir/π}` is algebraic for some non-zero rational `r`, then two of `π`, `e`, `e^{π²}` are
algebraically independent.

This is `DiazModulus.pi_e_exp_pi_sq_indep_of_exp_i_rat_div_pi` with its hypothesis `hW73`
discharged by Waldschmidt's theorem of 1973,
`DiazModulus.two_algebraically_independent_of_exp_column`. -/
theorem pi_e_exp_pi_sq_indep_of_exp_i_rat_div_pi_algebraic
    (r : ℚ) (hr : r ≠ 0)
    (halg : IsAlgebraic ℚ (Complex.exp (Complex.I * (r : ℂ) / ((Real.pi : ℝ) : ℂ)))) :
    ∃ a ∈ ({((Real.pi : ℝ) : ℂ), Complex.exp 1, Complex.exp (((Real.pi : ℝ) : ℂ) ^ 2)} : Set ℂ),
      ∃ b ∈ ({((Real.pi : ℝ) : ℂ), Complex.exp 1, Complex.exp (((Real.pi : ℝ) : ℂ) ^ 2)} : Set ℂ),
        AlgebraicIndependent ℚ ![a, b] := by
  sorry

end DiazModulus
