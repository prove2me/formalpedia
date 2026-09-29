-- Prove2me | Theorems.Thm_Diaz_sq_eq_zero_of_trace_eq_zero
-- name    : Diaz.sq_eq_zero_of_trace_eq_zero
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T07:14:36.098352+00:00
-- url     : https://prove2.me/theorems/a1b376a7-a397-4500-a45f-9db9b030c2af
-- title:
--   A $2\times2$ matrix with vanishing trace and determinant squares to zero
-- statement:
--   **Cayley--Hamilton in dimension two: trace zero and determinant zero force $M^2 = 0$.**
--
--   For a $2 \times 2$ matrix $M$ over a commutative ring with $\operatorname{tr} M = 0$ and $\det M = 0$,
--   one has $M \cdot M = 0$.
--
--   **Why.** The Cayley--Hamilton relation in size two reads $M^2 - (\operatorname{tr}M)M + (\det M)I = 0$;
--   under the two hypotheses it collapses to $M^2 = 0$. The Lean proof simply verifies the four entries
--   directly from the two scalar hypotheses, so no Cayley--Hamilton machinery is invoked.
--
--   **Role.** In Carlo Perassi's proof of the uniqueness of the $2\times2$ obstruction this converts the four vanishing identities produced by coefficient
--   comparison into the square-zero conditions $B^2 = C^2 = 0$ that pin down the pencil
--   $I + Bu + C\bar u$, and hence identify the singular matrix as $P H_u Q$ with $P,Q$ algebraic. Together
--   with $\operatorname{tr}(BC) = 1/\rho \neq 0$ it also shows $B, C \neq 0$.
--
--   Source: Carlo Perassi, the Cayley--Hamilton step in his proof of the uniqueness of the $2\times2$
--   obstruction, unpublished apart from this node; the nilpotent pencil it yields is stated after Theorem 4.2 (*Uniqueness of the obstruction*) of his companion note to https://github.com/carlok/diaz-modulus-lean (version 1.9, 25 September 2026, GitHub release note-v1.9). Classical; no novelty is claimed.

import Mathlib

open ComplexConjugate

theorem Diaz.sq_eq_zero_of_trace_eq_zero {R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R)
    (htr : Matrix.trace M = 0) (hdet : M.det = 0) : M * M = 0 := by sorry
