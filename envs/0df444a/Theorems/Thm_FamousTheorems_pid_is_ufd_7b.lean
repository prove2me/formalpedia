-- Prove2me | Theorems.Thm_FamousTheorems_pid_is_ufd_7b
-- name    : FamousTheorems.pid_is_ufd_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:32:36.244602+00:00
-- url     : https://prove2.me/theorems/6afa2a75-c198-44b9-8465-85bab283301a
-- title:
--   Every principal ideal domain is a unique factorization domain
-- statement:
--   **Every principal ideal domain is a unique factorization domain.** Let $R$ be an integral domain in which every ideal is principal. Then every nonzero nonunit of $R$ is a product of irreducible elements, and this factorization is unique up to order and multiplication by units.
--
--   This is the classical route to unique factorization in $\mathbb Z$, in $k[X]$ for a field $k$, and in the Gaussian integers. The proof has two parts: principal ideal domains are Noetherian, so factorizations into irreducibles exist, and irreducible elements generate maximal ideals and are therefore prime, which gives uniqueness.
--
--   **Formalization note.** Mathlib's `PrincipalIdealRing.to_uniqueFactorizationMonoid`. `UniqueFactorizationMonoid R` says that every nonzero element has a factorization into irreducibles and that irreducible elements are prime. This is equivalent to the usual uniqueness condition.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `PrincipalIdealRing.to_uniqueFactorizationMonoid`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem pid_is_ufd_7b {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] : UniqueFactorizationMonoid R := by sorry

end FamousTheorems
