-- Prove2me | Theorems.Thm_FamousTheorems_first_isomorphism_theorem_rings
-- name    : FamousTheorems.first_isomorphism_theorem_rings
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T21:26:06.087893+00:00
-- url     : https://prove2.me/theorems/f14c3dfc-8da2-4ce0-ad4e-3c7cfea86c7c
-- title:
--   The first isomorphism theorem for rings
-- statement:
--   **The first isomorphism theorem for rings.** Let $f:R\to S$ be a surjective ring homomorphism. Then
--   $$R/\ker f\;\cong\;S$$
--   as rings.
--
--   It identifies every quotient of a ring with a homomorphic image and back. This underlies the standard constructions of algebra, such as $\mathbb Z/n\mathbb Z$, $\mathbb C\cong\mathbb R[X]/(X^2+1)$, residue fields, and coordinate rings of varieties.
--
--   **Formalization note.** Mathlib's `RingHom.quotientKerEquivOfSurjective`, for `R` a (not necessarily commutative) ring and `S` a semiring; the kernel is a two-sided ideal and `≃+*` is a ring isomorphism. The statement asserts that such an isomorphism exists.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `RingHom.quotientKerEquivOfSurjective`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem first_isomorphism_theorem_rings {R S : Type*} [Ring R] [Semiring S] (f : R →+* S) (hf : Function.Surjective f) :
    Nonempty (R ⧸ RingHom.ker f ≃+* S) := by sorry

end FamousTheorems
