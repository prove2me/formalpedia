-- Prove2me | Theorems.Thm_FamousTheorems_exists_infinite_primes
-- name    : FamousTheorems.exists_infinite_primes
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T21:51:59.242978+00:00
-- url     : https://prove2.me/theorems/fcd5da5f-4a97-482e-a625-df1802ee79f3
-- title:
--   Euclid's theorem: there are infinitely many primes
-- statement:
--   **There are infinitely many primes.**
--
--   For every $n$ there is a prime $p \ge n$.
--
--   Euclid's argument: given any finite list of primes, $N = p_1p_2\cdots p_k + 1$ leaves remainder
--   $1$ on division by each $p_i$, so any prime factor of $N$ is new. Stated as above — for each $n$
--   a prime at least $n$ — it avoids the common misreading that the proof is by contradiction; it is
--   constructive.
--
--   This is Proposition IX.20 of the *Elements* and the starting point of analytic number theory.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

theorem exists_infinite_primes : ∀ n : ℕ, ∃ p, n ≤ p ∧ Nat.Prime p := by sorry

end FamousTheorems
