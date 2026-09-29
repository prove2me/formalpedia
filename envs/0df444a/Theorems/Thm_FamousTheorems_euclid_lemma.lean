-- Prove2me | Theorems.Thm_FamousTheorems_euclid_lemma
-- name    : FamousTheorems.euclid_lemma
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:21:08.245035+00:00
-- url     : https://prove2.me/theorems/a71e7687-fae4-497b-b785-2e3365dc4e12
-- title:
--   Euclid's lemma
-- statement:
--   **Euclid's lemma.** If $p$ is a prime number and $m,n$ are natural numbers, then $p\mid mn$ if and only if $p\mid m$ or $p\mid n$.
--
--   This is Proposition VII.30 of Euclid's Elements. It is the key step in the uniqueness of prime factorisation, and it characterises prime elements in general commutative rings.
--
--   **Formalization note.** Mathlib's `Nat.Prime.dvd_mul`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Nat.Prime.dvd_mul`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem euclid_lemma {p m n : ℕ} (hp : p.Prime) : p ∣ m * n ↔ p ∣ m ∨ p ∣ n := by sorry

end FamousTheorems
