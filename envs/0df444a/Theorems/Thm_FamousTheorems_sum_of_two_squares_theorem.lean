-- Prove2me | Theorems.Thm_FamousTheorems_sum_of_two_squares_theorem
-- name    : FamousTheorems.sum_of_two_squares_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:57:45.708767+00:00
-- url     : https://prove2.me/theorems/d89f6ea0-deae-4bc1-a30f-e96a2162c2dc
-- title:
--   The sum of two squares theorem
-- statement:
--   **The sum of two squares theorem.** A natural number $n$ is a sum of two squares of natural numbers if and only if every prime $q\equiv3\pmod4$ appears in the prime factorization of $n$ with even exponent.
--
--   This combines Fermat's theorem on primes $p\equiv1\pmod4$ being sums of two squares with the multiplicativity of sums of two squares (Brahmagupta–Fibonacci identity). It is a model result for the arithmetic of quadratic forms and of the Gaussian integers.
--
--   **Formalization note.** Mathlib's `Nat.eq_sq_add_sq_iff`. `n.primeFactors` is the set of primes dividing $n$, and `padicValNat q n` is the exponent of $q$ in $n$. For $n=0$ both sides hold, since $0=0^2+0^2$ and $0$ has no prime factors.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Nat.eq_sq_add_sq_iff`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem sum_of_two_squares_theorem {n : ℕ} : (∃ x y : ℕ, n = x ^ 2 + y ^ 2) ↔ ∀ q ∈ n.primeFactors, q % 4 = 3 → Even (padicValNat q n) := by sorry

end FamousTheorems
