-- Prove2me | Theorems.Thm_FCP_Zeta_irrational_zeta_odd
-- name    : FCP.Zeta.irrational_zeta_odd
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-15T20:53:49.381244+00:00
-- url     : https://prove2.me/theorems/0139e9a9-aacb-430f-b3e5-191a9ba5f37f
-- title:
--   Irrationality of $\zeta(2n+1)$ for every $n \ge 1$
-- statement:
--   **Irrationality of all odd zeta values.** For every integer $n \ge 1$, $\zeta(2n+1)$ is irrational. Only $\zeta(3)$ is known (Apéry, 1978); Rivoal and Ball--Rivoal showed that infinitely many odd zeta values are irrational, and Zudilin located an irrational one among $\zeta(5), \zeta(7), \zeta(9), \zeta(11)$.
-- source:
--   Formal Conjectures library (Google DeepMind), Apache-2.0, https://github.com/google-deepmind/formal-conjectures (FormalConjectures/Wikipedia/RiemannZetaValues.lean); https://en.wikipedia.org/wiki/Particular_values_of_the_Riemann_zeta_function

import Mathlib

namespace FCP.Zeta

theorem irrational_zeta_odd (n : ℕ) (hn : 0 < n) :
    ∃ x : ℝ, Irrational x ∧ riemannZeta (2 * n + 1) = x := by sorry

end FCP.Zeta
