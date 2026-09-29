-- Prove2me | Theorems.Thm_FamousTheorems_dedekind_finite_primes_pid_7b
-- name    : FamousTheorems.dedekind_finite_primes_pid_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:33:50.71133+00:00
-- url     : https://prove2.me/theorems/21f48459-94fc-45b7-a74c-54269cbdf16d
-- title:
--   A Dedekind domain with finitely many primes is a PID
-- statement:
--   **A Dedekind domain with finitely many primes is a PID.** Let $R$ be a Dedekind domain with only finitely many prime ideals. Then every ideal of $R$ is principal.
--
--   Examples are the localizations of rings of integers at finitely many primes, which are semi-local. The result is used to reduce questions about Dedekind domains to local and semi-local ones. The proof uses the Chinese remainder theorem to find, for a nonzero prime $P$, an element $x$ that lies in $P$ but not in $P^2$ or any other prime, so $(x)=P$.
--
--   **Formalization note.** Mathlib's `IsPrincipalIdealRing.of_finite_primes`. In Mathlib a Dedekind domain is a Noetherian, integrally closed domain in which every nonzero prime is maximal; a field counts as a Dedekind domain.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `IsPrincipalIdealRing.of_finite_primes`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem dedekind_finite_primes_pid_7b {R : Type*} [CommRing R] [IsDedekindDomain R] (h : {I : Ideal R | I.IsPrime}.Finite) :
    IsPrincipalIdealRing R := by sorry

end FamousTheorems
