-- Prove2me | Theorems.Thm_FamousTheorems_going_up
-- name    : FamousTheorems.going_up
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:14:49.350876+00:00
-- url     : https://prove2.me/theorems/3f9983e6-1fc2-468a-aa29-761a3d1b7b3f
-- title:
--   The going-up theorem (Cohen–Seidenberg)
-- statement:
--   **The going-up theorem (Cohen–Seidenberg).** Let $S$ be an integral extension of a commutative ring $R$. Let $P$ be a prime of $R$ and $I$ a prime of $S$ lying below $P$, i.e. $I\cap R\subseteq P$. Then there is a prime $Q\supseteq I$ of $S$ lying over $P$: $Q\cap R=P$.
--
--   Chains of primes in $R$ therefore lift to chains in $S$, so integral extensions preserve Krull dimension. With lying-over and incomparability, going-up is the basic tool relating the prime spectra of $R$ and $S$ in commutative algebra and algebraic number theory.
--
--   **Formalization note.** Mathlib's `Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime`; primes are ideals with `IsPrime`, and "lying over" is `Ideal.comap (algebraMap R S) Q = P`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem going_up {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S] (P : Ideal R) [P.IsPrime]
    (I : Ideal S) [I.IsPrime] (hIP : Ideal.comap (algebraMap R S) I ≤ P) :
    ∃ Q ≥ I, Q.IsPrime ∧ Ideal.comap (algebraMap R S) Q = P := by sorry

end FamousTheorems
