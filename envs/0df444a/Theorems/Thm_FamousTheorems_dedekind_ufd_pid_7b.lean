-- Prove2me | Theorems.Thm_FamousTheorems_dedekind_ufd_pid_7b
-- name    : FamousTheorems.dedekind_ufd_pid_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:33:53.789624+00:00
-- url     : https://prove2.me/theorems/d4388b5a-1d47-4547-8bf5-175ae5491dfe
-- title:
--   A Dedekind domain that is a UFD is a PID
-- statement:
--   **A Dedekind domain with unique factorization is a PID.** Let $R$ be a Dedekind domain that is a unique factorization domain. Then $R$ is a principal ideal domain.
--
--   In a Dedekind domain the class group measures the failure of unique factorization of elements, and this theorem says that it vanishes as soon as unique factorization holds. For rings of integers of number fields, unique factorization is therefore equivalent to class number $1$. The proof shows that every nonzero prime contains a prime element, which generates a nonzero prime ideal and so equals it.
--
--   **Formalization note.** Mathlib's `IsPrincipalIdealRing.of_isDedekindDomain_of_uniqueFactorizationMonoid`. `UniqueFactorizationMonoid R` says that every nonzero element has a factorization into irreducibles and that irreducible elements are prime.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `IsPrincipalIdealRing.of_isDedekindDomain_of_uniqueFactorizationMonoid`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem dedekind_ufd_pid_7b (R : Type*) [CommRing R] [IsDedekindDomain R] [UniqueFactorizationMonoid R] : IsPrincipalIdealRing R := by sorry

end FamousTheorems
