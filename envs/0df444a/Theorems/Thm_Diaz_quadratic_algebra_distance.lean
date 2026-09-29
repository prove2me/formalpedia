-- Prove2me | Theorems.Thm_Diaz_quadratic_algebra_distance
-- name    : Diaz.quadratic_algebra_distance
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T07:14:32.776982+00:00
-- url     : https://prove2.me/theorems/77ea73b5-12ca-4e15-8a95-566bae86f8b9
-- title:
--   Three algebraic norms force the mixed product algebraic
-- statement:
--   **Source.** Carlo Perassi's p-adic algebraic distance and plane rigidity theorem — the
--   forward implication of its first equivalence, stated over an arbitrary quadratic algebra rather
--   than over a quadratic extension of `ℚ_p`.
--
--   **Statement.** Let `R` be a commutative ring, `σ` a ring involution, `A` a subring, and suppose `A`
--   absorbs the roots of monic quadratics over it: if `z² − p z + q = 0` with `p, q ∈ A` then `z ∈ A`.
--   If the three norms `u σ u`, `v σ v` and `(u − v) σ (u − v)` all lie in `A`, then so does the mixed
--   product `u σ v`.
--
--   **The mechanism.** Put `z = u σ v`. The trace–norm identity gives
--   `z + σ z = N u + N v − N (u − v) ∈ A` and `z σ z = N u * N v ∈ A`, and `z` is then a root of
--   `X² − (z + σ z) X + z σ z`, a monic quadratic over `A` — the vanishing is a bare ring identity.
--   The absorption hypothesis finishes it. Over `ℂ` with `A = ℚ̄` the hypothesis holds because the
--   algebraic numbers are algebraically closed in `ℂ`; over `ℂ_p` it holds for the same reason, which
--   is the point of the p-adic transfer.
--
--   **What this is not.** The full p-adic theorem concludes `v / u ∈ ℚ×`, and that last step
--   needs the p-adic Baker theorem (Brumer) to descend an algebraic linear relation to a rational one.
--   That input is not formalised here; this node is the part of the argument that is pure quadratic
--   algebra.
--
--   **Not in the companion note.** This statement is not in Carlo Perassi's companion note to https://github.com/carlok/diaz-modulus-lean (version 1.9, 25 September 2026, GitHub release note-v1.9), which does not treat the p-adic setting; it is unpublished apart from this node. Nothing here was withdrawn as wrong. It is worth recording because the argument is unconditional and short.
--
--   **Novelty.** No novelty is claimed.

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

theorem Diaz.quadratic_algebra_distance {R : Type*} [CommRing R] (σ : R →+* R) (hσ : ∀ x, σ (σ x) = x)
    (A : Subring R)
    (hquad : ∀ z p q : R, p ∈ A → q ∈ A → z * z - p * z + q = 0 → z ∈ A)
    {u v : R} (hu : u * σ u ∈ A) (hv : v * σ v ∈ A)
    (huv : (u - v) * σ (u - v) ∈ A) :
    u * σ v ∈ A := by sorry
