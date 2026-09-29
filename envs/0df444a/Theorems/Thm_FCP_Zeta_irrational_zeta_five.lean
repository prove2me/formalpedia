-- Prove2me | Theorems.Thm_FCP_Zeta_irrational_zeta_five
-- name    : FCP.Zeta.irrational_zeta_five
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-15T20:53:34.80769+00:00
-- url     : https://prove2.me/theorems/a4144d86-de86-4054-ad60-7b9a8f1c85a3
-- title:
--   Irrationality of $\zeta(5)$
-- statement:
--   **Is $\zeta(5)$ irrational?** The value $\zeta(5) = \sum_{n\ge1} n^{-5}$ is conjectured — and stated here — to be irrational. Apéry proved the irrationality of $\zeta(3)$ in 1978; for $\zeta(5)$ only partial results are known, e.g. Zudilin's theorem that one of $\zeta(5), \zeta(7), \zeta(9), \zeta(11)$ is irrational.
-- source:
--   Formal Conjectures library (Google DeepMind), Apache-2.0, https://github.com/google-deepmind/formal-conjectures (FormalConjectures/Wikipedia/RiemannZetaValues.lean); https://en.wikipedia.org/wiki/Particular_values_of_the_Riemann_zeta_function

import Mathlib

namespace FCP.Zeta

theorem irrational_zeta_five : ∃ x : ℝ, Irrational x ∧ riemannZeta 5 = x := by sorry

end FCP.Zeta
