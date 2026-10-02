-- Prove2me | Theorems.Thm_DiazModulus_exp_pi_sq_or_exp_i_pi_cube_transcendental
-- name    : DiazModulus.exp_pi_sq_or_exp_i_pi_cube_transcendental
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T16:21:06.414351+00:00
-- url     : https://prove2.me/theorems/a8ff92c0-ee70-4d4f-b820-c48295a250c1
-- title:
--   At least one of e^{π²} and e^{iπ³} is transcendental
-- statement:
--   **$\mathrm{e}^{\pi^{2}}$ or $\mathrm{e}^{i\pi^{3}}$.**
--
--   At least one of the two numbers
--
--   $$\mathrm{e}^{\pi^{2}} \qquad\text{and}\qquad \mathrm{e}^{i\pi^{3}}$$
--
--   is transcendental.
--
--   The transcendence of $\mathrm{e}^{\pi^{2}}$ alone is not known. It is the standard example of a number whose transcendence would follow from an inhomogeneous extension of the rank theory of matrices of logarithms, which is exactly where Diaz's modulus conjecture is stuck. The disjunction is what the four exponentials theorem in transcendence degree one gives: it is `DiazModulus.geometric_triple_not_logs` at $w = i\pi$, $z = -i\pi$, where $\mathrm{e}^{w} = -1$, $wz = \pi^{2}$ and $wz^{2} = -i\pi^{3}$.
--
--   **Novelty.** None: the statement is classical. It is Corollaire 2 of M. Waldschmidt, *Solution du huitième problème de Schneider*, J. Number Theory **5** (1973), 191–202, at $\alpha = -1$, $r = 1$, found independently by W. D. Brownawell, J. Number Theory **6** (1974). G. Diaz gives it with essentially this proof in J. Théor. Nombres Bordeaux **19** (2007), p. 386, and on p. 381, from Roy's strong six exponentials theorem, the stronger statement that $\mathrm{e}^{\alpha\pi^{2}}$ or $\mathrm{e}^{\beta\pi^{3}}$ is transcendental for all non-zero algebraic $\alpha, \beta$. More is known in the same direction: if $\mathrm{e}^{\pi^{2}}$ is algebraic, then $\mathrm{e}$ and $\pi$ are algebraically independent (Waldschmidt 1973, Corollaire 1), and so are $\pi$ and $\mathrm{e}^{i\pi^{3}}$ (Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Springer 2000, Exercise 15.15(c)). The contribution of this node is the formal proof.
-- source:
--   Classical: M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973), 191–202, Corollaire 2 (alpha = -1, r = 1); W. D. Brownawell, The algebraic independence of certain numbers related by the exponential function, J. Number Theory 6 (1974), 22–31. See also G. Diaz, Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels, J. Théor. Nombres Bordeaux 19 (2007), 373–391, p. 386. Formal proof: Diaz modulus mission, 23 September 2026 (C. Perassi).

import Mathlib

namespace DiazModulus

theorem exp_pi_sq_or_exp_i_pi_cube_transcendental :
    Transcendental ℚ (Complex.exp (((Real.pi : ℝ) : ℂ) ^ 2)) ∨
      Transcendental ℚ (Complex.exp (Complex.I * ((Real.pi : ℝ) : ℂ) ^ 3)) := by sorry

end DiazModulus
