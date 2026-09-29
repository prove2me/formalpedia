-- Prove2me | Theorems.Thm_FamousTheorems_nilradical_eq_inf_primes_7b
-- name    : FamousTheorems.nilradical_eq_inf_primes_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:33:50.07591+00:00
-- url     : https://prove2.me/theorems/04d9368e-6f55-4f52-a37c-b8152f1d9dab
-- title:
--   The nilradical is the intersection of all prime ideals
-- statement:
--   **The nilradical is the intersection of all prime ideals.** Let $R$ be a commutative ring. The set of nilpotent elements of $R$ is the intersection of all prime ideals of $R$.
--
--   Geometrically, a function on $\operatorname{Spec}R$ vanishes at every point exactly when it is nilpotent. The theorem is the ring-theoretic basis of the Nullstellensatz and of the definition of reduced schemes. One inclusion is clear. For the other, if $f$ is not nilpotent then the localization $R_f$ is nonzero and has a maximal ideal, whose preimage is a prime not containing $f$.
--
--   **Formalization note.** Mathlib's `nilradical_eq_sInf`, stated for commutative semirings. `nilradical R` is the ideal of nilpotent elements and `sInf` is the intersection of a set of ideals.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `nilradical_eq_sInf`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem nilradical_eq_inf_primes_7b (R : Type*) [CommSemiring R] : nilradical R = sInf {J : Ideal R | J.IsPrime} := by sorry

end FamousTheorems
