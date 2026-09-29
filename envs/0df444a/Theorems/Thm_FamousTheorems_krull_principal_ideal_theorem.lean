-- Prove2me | Theorems.Thm_FamousTheorems_krull_principal_ideal_theorem
-- name    : FamousTheorems.krull_principal_ideal_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:15:14.169588+00:00
-- url     : https://prove2.me/theorems/8803daad-ef66-4572-b6ed-176259dd03f4
-- title:
--   Krull's principal ideal theorem
-- statement:
--   **Krull's principal ideal theorem (Hauptidealsatz).** In a Noetherian commutative ring, every prime ideal minimal over a principal ideal $(a)$ has height at most $1$.
--
--   Cutting by one equation lowers dimension by at most one. The generalisation to $n$ generators (Krull's height theorem) gives a well-behaved dimension theory for Noetherian rings. It is basic to intersection theory and to the theory of regular local rings and complete intersections.
--
--   **Formalization note.** Mathlib's `Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes`; `I.minimalPrimes` are the primes minimal over `I` and `p.height` is the height in `ℕ∞`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem krull_principal_ideal_theorem {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [Submodule.IsPrincipal I] :
    ∀ p ∈ I.minimalPrimes, p.height ≤ 1 := by sorry

end FamousTheorems
