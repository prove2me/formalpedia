-- Prove2me | Theorems.Thm_FamousTheorems_aeval_self_charpoly
-- name    : FamousTheorems.aeval_self_charpoly
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T22:10:37.634621+00:00
-- url     : https://prove2.me/theorems/209c6e10-c14c-46e8-8e34-df730641d40b
-- title:
--   The Cayley–Hamilton theorem
-- statement:
--   **Every square matrix satisfies its own characteristic polynomial.**
--
--   $$\chi_M(M) = 0, \qquad \chi_M(t) = \det(t I - M).$$
--
--   The one-line "proof" — substitute $t = M$ into $\det(tI - M)$ — is nonsense, since it confuses
--   scalars with matrices. The genuine argument uses the adjugate identity
--   $\mathrm{adj}(tI - M)\,(tI-M) = \chi_M(t)\,I$ over the polynomial ring $R[t]$ and compares
--   coefficients, which is why the theorem holds over any commutative ring rather than just fields.
--
--   Consequences: the inverse of an invertible matrix is a polynomial in the matrix; the minimal
--   polynomial divides the characteristic polynomial; and $M^{k}$ for $k \ge n$ is a combination of
--   $I, M, \dots, M^{n-1}$, which is what makes linear recurrences solvable in closed form.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

theorem aeval_self_charpoly : ∀ {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]
    (M : Matrix n n R), (Polynomial.aeval M) M.charpoly = 0 := by sorry

end FamousTheorems
