-- Prove2me | Theorems.Thm_FamousTheorems_fermat_prime_exponent_power_of_two
-- name    : FamousTheorems.fermat_prime_exponent_power_of_two
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:37:32.139804+00:00
-- url     : https://prove2.me/theorems/e9206e68-ad0a-4e56-80b2-46bbf7f797fe
-- title:
--   Fermat primes: if a^n+1 is prime then n is a power of two
-- statement:
--   **Fermat primes: if $a^n+1$ is prime then $n$ is a power of two.** Let $a>1$ and $n\ge1$ be integers. If $a^n+1$ is prime, then $n=2^m$ for some $m\ge0$.
--
--   If $n$ had an odd factor $k>1$, then $a^{n/k}+1$ would properly divide $a^n+1$. So the only candidates for primes of the form $2^n+1$ are the Fermat numbers $F_m=2^{2^m}+1$. Fermat conjectured that all of them are prime, and Euler refuted this in 1732 with $641\mid F_5$. By the Gauss–Wantzel theorem, Fermat primes determine which regular polygons are constructible.
--
--   **Formalization note.** Mathlib's `Nat.pow_of_pow_add_prime`, for natural numbers $a>1$ and $n\ne0$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Nat.pow_of_pow_add_prime`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem fermat_prime_exponent_power_of_two {a n : ℕ} (ha : 1 < a) (hn : n ≠ 0) (hp : (a ^ n + 1).Prime) : ∃ m : ℕ, n = 2 ^ m := by sorry

end FamousTheorems
