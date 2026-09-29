-- Prove2me | Theorems.Thm_FCP_Kaplansky_zero_divisor_conjecture
-- name    : FCP.Kaplansky.zero_divisor_conjecture
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-15T20:52:35.867671+00:00
-- url     : https://prove2.me/theorems/e85efc1b-ba95-4808-9840-76f501a58870
-- title:
--   Kaplansky's zero-divisor conjecture
-- statement:
--   **Kaplansky's zero-divisor conjecture.** If $G$ is a torsion-free group and $K$ is a field, then the group algebra $K[G]$ has no zero divisors. Torsion-freeness is necessary: if $g$ has order $n > 1$ then $(1-g)(1+g+\cdots+g^{n-1}) = 0$. The conjecture is known for large classes of groups (orderable groups, unique-product groups, hyperbolic groups by Delzant), and is open in general; the closely related unit conjecture was disproved by Gardam in 2021.
-- source:
--   Formal Conjectures library (Google DeepMind), Apache-2.0, https://github.com/google-deepmind/formal-conjectures (FormalConjectures/Wikipedia/Kaplansky.lean); https://en.wikipedia.org/wiki/Kaplansky%27s_conjectures

import Mathlib

namespace FCP.Kaplansky

theorem zero_divisor_conjecture (K : Type) [Field K] (G : Type) [Group G]
    (hG : ∀ g : G, IsOfFinOrder g → g = 1) : NoZeroDivisors (MonoidAlgebra K G) := by sorry

end FCP.Kaplansky
