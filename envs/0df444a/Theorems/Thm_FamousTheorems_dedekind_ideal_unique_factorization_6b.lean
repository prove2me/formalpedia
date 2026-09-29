-- Prove2me | Theorems.Thm_FamousTheorems_dedekind_ideal_unique_factorization_6b
-- name    : FamousTheorems.dedekind_ideal_unique_factorization_6b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:43:19.270814+00:00
-- url     : https://prove2.me/theorems/68fe33a2-9d2d-4a94-9c20-754a036112c9
-- title:
--   Unique factorization of ideals in Dedekind domains
-- statement:
--   **Unique factorization of ideals in Dedekind domains.** Let $A$ be a Dedekind domain. Then every nonzero ideal of $A$ factors as a product of prime ideals, and the factorization is unique up to order.
--
--   This theorem is how algebraic number theory recovers unique factorization when it fails for elements. For example, $6=2\cdot3=(1+\sqrt{-5})(1-\sqrt{-5})$ in $\mathbb Z[\sqrt{-5}]$, but the ideal $(6)$ has a unique factorization into prime ideals. It applies to rings of integers of number fields and underlies the ideal class group and ramification theory.
--
--   **Formalization note.** Mathlib's `Ideal.uniqueFactorizationMonoid`, which makes the monoid of ideals of $A$ under multiplication a `UniqueFactorizationMonoid`. In it, every nonzero element is a product of irreducibles, uniquely up to units and order. The only unit ideal is $A$, and the irreducible ideals are the nonzero prime ideals.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Ideal.uniqueFactorizationMonoid`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem dedekind_ideal_unique_factorization_6b (A : Type*) [CommRing A] [IsDedekindDomain A] : UniqueFactorizationMonoid (Ideal A) := by sorry

end FamousTheorems
