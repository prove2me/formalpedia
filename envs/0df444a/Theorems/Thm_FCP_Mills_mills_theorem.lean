-- Prove2me | Theorems.Thm_FCP_Mills_mills_theorem
-- name    : FCP.Mills.mills_theorem
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-15T20:49:02.440689+00:00
-- url     : https://prove2.me/theorems/6bc42c06-cc1a-4051-af03-cfe31ce242b6
-- title:
--   Mills' theorem: a prime-representing constant exists
-- statement:
--   **Mills' theorem (1947).** There exists a real number $A > 1$ such that $\lfloor A^{3^{n}} \rfloor$ is prime for every integer $n \ge 1$. Mills' proof uses Ingham's theorem on prime gaps, $p_{n+1} - p_n = O(p_n^{5/8})$, to build $A$ as the limit of an increasing sequence of prime-indexed approximations. The least such $A$ is Mills' constant, $\approx 1.3063778838$ under the Riemann hypothesis.
-- source:
--   Formal Conjectures library (Google DeepMind), Apache-2.0, https://github.com/google-deepmind/formal-conjectures (FormalConjectures/Wikipedia/Mills.lean); W. H. Mills, A prime-representing function, Bull. Amer. Math. Soc. 53 (1947), 604

import Mathlib
import Definitions.Def_FCP_Mills

namespace FCP.Mills

theorem mills_theorem : ∃ A : ℝ, 1 < A ∧ IsMills A := by sorry

end FCP.Mills
