-- Prove2me | Theorems.Thm_FCP_Mersenne_infinitely_many_mersenne_primes
-- name    : FCP.Mersenne.infinitely_many_mersenne_primes
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-15T20:47:59.198977+00:00
-- url     : https://prove2.me/theorems/262a38c3-863c-420c-a57d-a8914b5aa9e6
-- title:
--   Infinitude of Mersenne primes
-- statement:
--   **Are there infinitely many Mersenne primes?** The conjecture — stated here in the affirmative, as the target to prove or disprove — is that the set of natural numbers $p$ for which $2^p - 1$ is prime is infinite. The Lenstra--Pomerance--Wagstaff heuristic predicts about $e^{\gamma}\log_2 x$ such $p$ below $x$; $52$ Mersenne primes are known.
-- source:
--   Formal Conjectures library (Google DeepMind), Apache-2.0, https://github.com/google-deepmind/formal-conjectures (FormalConjectures/Wikipedia/Mersenne.lean); https://en.wikipedia.org/wiki/Mersenne_prime

import Mathlib

namespace FCP.Mersenne

theorem infinitely_many_mersenne_primes : {p : ℕ | (mersenne p).Prime}.Infinite := by sorry

end FCP.Mersenne
