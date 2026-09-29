-- Prove2me | Theorems.Thm_FamousTheorems_mulVec_cramer
-- name    : FamousTheorems.mulVec_cramer
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T22:17:12.44662+00:00
-- url     : https://prove2.me/theorems/11dac367-c765-4c1d-8a8b-6c1dfd5e175e
-- title:
--   Cramer's rule
-- statement:
--   **Cramer's rule.**
--
--   $$A \cdot \mathrm{cramer}(A, b) \;=\; \det(A)\; b,$$
--   where the $i$-th entry of $\mathrm{cramer}(A,b)$ is $\det(A_i)$, the determinant of $A$ with its
--   $i$-th column replaced by $b$.
--
--   When $\det A$ is invertible this gives the solution of $Ax = b$ as $x_i = \det(A_i)/\det(A)$.
--   Stated multiplicatively as above it needs no invertibility and holds over **any commutative
--   ring**, which is the form that matters for adjugates and for integrality arguments.
--
--   As an algorithm it is hopeless — $n+1$ determinants against Gaussian elimination's $O(n^3)$ —
--   but as an identity it is the basis of the adjugate formula $A\,\mathrm{adj}(A) = \det(A) I$, and
--   hence of Cayley–Hamilton and of criteria for solvability over rings.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

theorem mulVec_cramer : ∀ {n : Type*} {α : Type*} [DecidableEq n] [Fintype n] [CommRing α]
    (A : Matrix n n α) (b : n → α), A.mulVec (A.cramer b) = A.det • b := by sorry

end FamousTheorems
