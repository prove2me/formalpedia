-- Prove2me | Theorems.Thm_FamousTheorems_eisenstein_criterion
-- name    : FamousTheorems.eisenstein_criterion
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T07:14:53.157967+00:00
-- url     : https://prove2.me/theorems/7575bf5e-a777-40b3-b0ca-0bc8956f1a8c
-- title:
--   Eisenstein's criterion
-- statement:
--   **Eisenstein's criterion** for irreducibility.
--
--   Let $f$ be a primitive polynomial over an integral domain and $P$ a prime ideal such that the
--   leading coefficient is not in $P$, every lower coefficient is in $P$, and the constant term is
--   not in $P^2$. Then $f$ is irreducible.
--
--   The classical case takes $P = (p)$ over $\mathbb{Z}$: if $p$ divides every coefficient except
--   the leading one, and $p^2$ does not divide the constant term, then $f$ is irreducible over
--   $\mathbb{Q}$. So $x^n - 2$ is irreducible for every $n$, giving degree-$n$ field extensions
--   at will.
--
--   The condition on $P^2$ is what makes the criterion sharp — without it $x^2 - p^2$ would
--   qualify while factoring as $(x-p)(x+p)$. Primitivity is needed so that irreducibility over the
--   fraction field transfers back to the polynomial ring (Gauss's lemma).
--
--   The standard application is the $p$-th cyclotomic polynomial: substituting $x \mapsto x+1$ in
--   $1 + x + \cdots + x^{p-1}$ produces an Eisenstein polynomial at $p$, proving irreducibility
--   and hence that $[\mathbb{Q}(\zeta_p):\mathbb{Q}] = p-1$.
--
--   Eisenstein published it in 1850; Schönemann had it four years earlier.
--
--   **Formalization note.** `f.degree` lives in `WithBot ℕ`, so the coefficient hypothesis is
--   stated with a cast; `f.IsPrimitive` says the content is a unit. The result is Mathlib's
--   `Polynomial.irreducible_of_eisenstein_criterion`.
-- source:
--   Listed in Mathlib's undergraduate/overview curriculum manifests (docs/undergrad.yaml, docs/overview.yaml); formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u v

open Filter Set Topology DirectSum

theorem eisenstein_criterion {R : Type*} [CommRing R] [IsDomain R] {f : Polynomial R}
    {P : Ideal R} (hP : P.IsPrime) (hfl : f.leadingCoeff ∉ P)
    (hfP : ∀ n : ℕ, (n : WithBot ℕ) < f.degree → f.coeff n ∈ P) (hfd0 : 0 < f.degree)
    (h0 : f.coeff 0 ∉ P ^ 2) (hu : f.IsPrimitive) : Irreducible f := by sorry

end FamousTheorems
