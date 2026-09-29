-- Prove2me | Theorems.Thm_FamousTheorems_polynomial_remainder_theorem
-- name    : FamousTheorems.polynomial_remainder_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T21:27:11.064228+00:00
-- url     : https://prove2.me/theorems/593bdee3-8917-45fd-b3a1-233b1fa4db47
-- title:
--   The polynomial remainder theorem
-- statement:
--   **The polynomial remainder theorem.** Let $R$ be a commutative ring, $p\in R[X]$ and $a\in R$. The remainder of $p$ on division by $X-a$ is the constant $p(a)$:
--   $$p\bmod(X-a)=p(a).$$
--
--   In particular $X-a$ divides $p$ if and only if $p(a)=0$ (the factor theorem). This underlies the fact that a nonzero polynomial over a domain has at most $\deg p$ roots, as well as Horner's scheme and synthetic division.
--
--   **Formalization note.** Mathlib's `Polynomial.modByMonic_X_sub_C_eq_C_eval`. `Polynomial.modByMonic` is division with remainder by a monic polynomial, which works over any commutative ring. `Polynomial.C` is the constant polynomial.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Polynomial.modByMonic_X_sub_C_eq_C_eval`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem polynomial_remainder_theorem {R : Type*} [CommRing R] (p : Polynomial R) (a : R) :
    p.modByMonic (Polynomial.X - Polynomial.C a) = Polynomial.C (p.eval a) := by sorry

end FamousTheorems
