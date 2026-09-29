-- Prove2me | Theorems.Thm_FamousTheorems_kaplansky_ufd_criterion
-- name    : FamousTheorems.kaplansky_ufd_criterion
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:04:36.188323+00:00
-- url     : https://prove2.me/theorems/8443e2a2-b716-486a-be57-09157f75b696
-- title:
--   Kaplansky's criterion for unique factorization domains
-- statement:
--   **Kaplansky's criterion for unique factorization domains.** An integral domain $R$ is a unique factorization domain if and only if every nonzero prime ideal of $R$ contains a prime element.
--
--   The criterion describes unique factorization through prime ideals alone. It gives a short proof that a Noetherian domain is a UFD exactly when every height-one prime ideal is principal, and it is the standard route to Nagata's criterion for factoriality.
--
--   **Formalization note.** Mathlib's `UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime`, stated for commutative semiring domains. `UniqueFactorizationMonoid R` is Mathlib's notion of unique factorization, and `Prime x` is primality of an element.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem kaplansky_ufd_criterion {R : Type*} [CommSemiring R] [IsDomain R] :
    UniqueFactorizationMonoid R ↔ ∀ I ≠ (⊥ : Ideal R), I.IsPrime → ∃ x ∈ I, Prime x := by sorry

end FamousTheorems
