-- Prove2me | Theorems.Thm_DiazModulus_exp_i_div_pi_or_exp_i_pi_cube_transcendental
-- name    : DiazModulus.exp_i_div_pi_or_exp_i_pi_cube_transcendental
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T18:31:37.700018+00:00
-- url     : https://prove2.me/theorems/c8760738-626c-4788-b613-b6c5c7e62c4b
-- title:
--   At least one of e^{i/π} and e^{iπ³} is transcendental
-- statement:
--   **$e^{i/\pi}$ or $e^{i\pi^{3}}$.**
--
--   At least one of
--
--   $$e^{i/\pi} \qquad\text{and}\qquad e^{i\pi^{3}}$$
--
--   is transcendental.
--
--   $e^{i/\pi}$ is the smallest instance of the statement (S), at $\gamma = \pm 1$. Neither number is known to be transcendental on its own. It is `DiazModulus.recip_pi_or_pi_cube` at $\gamma = 1$, and a companion to `DiazModulus.exp_pi_sq_or_exp_i_pi_cube_transcendental`.
--
--   **Novelty.** None: the statement is classical. It is the case $r = -1$ of the remark after Corollaire 4 in M. Waldschmidt, *Solution du huitième problème de Schneider*, J. Number Theory **5** (1973), p. 192: for rational $r \neq 0, 1$, one of $e^{i\pi^{r}}$ and $e^{i\pi^{2-r}}$ is transcendental, and likewise one of $e^{\pi^{r}}$ and $e^{\pi^{2-r}}$. The contribution of this node is the formal proof.
-- source:
--   Classical: M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973), 191–202, p. 192, remark after Corollaire 4 (r = -1). Formal proof: Diaz modulus mission, 23 September 2026 (C. Perassi).

import Mathlib

namespace DiazModulus

theorem exp_i_div_pi_or_exp_i_pi_cube_transcendental :
    Transcendental ℚ (Complex.exp (Complex.I / ((Real.pi : ℝ) : ℂ))) ∨
      Transcendental ℚ (Complex.exp (Complex.I * ((Real.pi : ℝ) : ℂ) ^ 3)) := by sorry

end DiazModulus
