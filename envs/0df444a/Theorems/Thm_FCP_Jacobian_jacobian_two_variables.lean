-- Prove2me | Theorems.Thm_FCP_Jacobian_jacobian_two_variables
-- name    : FCP.Jacobian.jacobian_two_variables
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-15T20:53:22.219336+00:00
-- url     : https://prove2.me/theorems/54fd299c-e9b0-490c-97f0-4cbef88de8fc
-- title:
--   Jacobian conjecture in two variables
-- statement:
--   **The two-variable Jacobian conjecture.** Let $k$ be a field of characteristic $0$. If $F = (F_1, F_2)$ is a pair of polynomials in $k[X_0, X_1]$ whose Jacobian determinant is a unit (equivalently a nonzero constant), then $F$ has a polynomial inverse. Even this case is open, despite a long list of published false proofs; partial results bound the degrees of possible counterexamples. Note that the characteristic-zero hypothesis is essential, and that the conjecture as stated for *all* numbers of variables over a general commutative ring is false — the source library records an explicit three-variable counterexample.
-- source:
--   Formal Conjectures library (Google DeepMind), Apache-2.0, https://github.com/google-deepmind/formal-conjectures (FormalConjectures/Wikipedia/JacobianConjecture.lean); https://en.wikipedia.org/wiki/Jacobian_conjecture

import Mathlib
import Definitions.Def_FCP_Jacobian

namespace FCP.Jacobian

theorem jacobian_two_variables (k : Type) [Field k] [CharZero k] :
    JacobianConjectureProp k 2 := by sorry

end FCP.Jacobian
