-- Prove2me | Theorems.Thm_FamousTheorems_primeFactorsList_unique
-- name    : FamousTheorems.primeFactorsList_unique
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T21:55:18.952395+00:00
-- url     : https://prove2.me/theorems/50699c35-9b63-4c05-83a5-619089e26552
-- title:
--   The fundamental theorem of arithmetic
-- statement:
--   **Prime factorisation is unique up to order.**
--
--   Any list of primes whose product is $n$ is a permutation of $n$'s canonical prime factorisation.
--
--   Existence is easy induction; uniqueness is the content, and it rests on Euclid's lemma — if a
--   prime divides a product it divides a factor — which in turn comes from Bézout's identity. Without
--   it uniqueness genuinely fails: in $\mathbb{Z}[\sqrt{-5}]$ one has
--   $6 = 2\cdot3 = (1+\sqrt{-5})(1-\sqrt{-5})$ with all four factors irreducible.
--
--   That failure is precisely what motivated Kummer's ideal numbers and Dedekind's ideals, so this
--   theorem marks the boundary where elementary number theory ends and algebraic number theory
--   begins.
--
--   **Formalization note.** Stated as a `List.Perm` against Mathlib's canonical
--   `Nat.primeFactorsList`, which is the uniqueness assertion.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

theorem primeFactorsList_unique : ∀ {n : ℕ} {l : List ℕ}, l.prod = n → (∀ p ∈ l, Nat.Prime p) →
    l.Perm n.primeFactorsList := by sorry

end FamousTheorems
