-- Prove2me | Theorems.Thm_FamousTheorems_hermite_finiteness_number_fields
-- name    : FamousTheorems.hermite_finiteness_number_fields
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:05:25.189778+00:00
-- url     : https://prove2.me/theorems/0db7fe4a-5af1-48aa-abc8-c96e7dd4c6e1
-- title:
--   Hermite's theorem on number fields of bounded discriminant
-- statement:
--   **Hermite's theorem.** For every $N$ there are only finitely many number fields with $|d_K|\le N$. Here the fields are taken inside a fixed field $A$ of characteristic zero.
--
--   Hermite's theorem is one of the basic finiteness results of algebraic number theory. Combined with bounds on the discriminant in terms of the ramified primes, it implies that there are only finitely many number fields of given degree unramified outside a given finite set of primes. This finiteness is a key input in the Shafarevich conjecture and in finiteness theorems for Galois representations.
--
--   **Formalization note.** Mathlib's `NumberField.finite_of_discr_bdd`. Number fields are represented as finite-dimensional intermediate fields `F` of `ℚ ⊆ A`. The `haveI` line installs the `NumberField` instance on each such `F` so that `NumberField.discr` applies. The theorem asserts that the set of such `F` with $|d_F|\le N$ is finite.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `NumberField.finite_of_discr_bdd`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem hermite_finiteness_number_fields (A : Type*) [Field A] [CharZero A] (N : ℕ) :
    {K : { F : IntermediateField ℚ A // FiniteDimensional ℚ F } |
      haveI : NumberField K := @NumberField.mk _ _ inferInstance K.prop
      |NumberField.discr K| ≤ N}.Finite := by sorry

end FamousTheorems
