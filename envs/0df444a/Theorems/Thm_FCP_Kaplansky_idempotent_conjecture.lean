-- Prove2me | Theorems.Thm_FCP_Kaplansky_idempotent_conjecture
-- name    : FCP.Kaplansky.idempotent_conjecture
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-15T20:52:48.545879+00:00
-- url     : https://prove2.me/theorems/117964b9-3bbf-4460-96e4-e4cf0e30b8e8
-- title:
--   Kaplansky's idempotent conjecture
-- statement:
--   **Kaplansky's idempotent conjecture.** If $G$ is torsion-free and $K$ is a field, the only idempotents of $K[G]$ are $0$ and $1$. The conjecture follows from the zero-divisor conjecture, and is implied by the Baum--Connes conjecture with coefficients for many groups; Kadison--Kaplansky is the operator-algebra analogue.
-- source:
--   Formal Conjectures library (Google DeepMind), Apache-2.0, https://github.com/google-deepmind/formal-conjectures (FormalConjectures/Wikipedia/Kaplansky.lean); https://en.wikipedia.org/wiki/Kaplansky%27s_conjectures

import Mathlib

namespace FCP.Kaplansky

theorem idempotent_conjecture (K : Type) [Field K] (G : Type) [Group G]
    (hG : ∀ g : G, IsOfFinOrder g → g = 1) (a : MonoidAlgebra K G) (ha : IsIdempotentElem a) :
    a = 0 ∨ a = 1 := by sorry

end FCP.Kaplansky
