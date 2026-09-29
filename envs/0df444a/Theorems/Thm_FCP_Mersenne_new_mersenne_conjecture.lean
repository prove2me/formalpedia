-- Prove2me | Theorems.Thm_FCP_Mersenne_new_mersenne_conjecture
-- name    : FCP.Mersenne.new_mersenne_conjecture
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-15T20:44:52.68368+00:00
-- url     : https://prove2.me/theorems/1be6b715-6e4e-4603-9fd9-67de40f25a8b
-- title:
--   New Mersenne conjecture (Bateman--Selfridge--Wagstaff)
-- statement:
--   **The New Mersenne conjecture.** For every odd natural number $p$, if any two of the following three conditions hold, then so does the third:
--
--   1. $2^p - 1$ is prime (a Mersenne prime);
--   2. $(2^p+1)/3$ is prime (a Wagstaff prime);
--   3. $p = 2^k \pm 1$ or $p = 4^k \pm 3$ for some $k$.
--
--   The conjecture, due to Bateman, Selfridge and Wagstaff, has been verified for all $p$ up to very large bounds. It is stated here for all odd $p$; it suffices to check odd primes, and it genuinely fails at $p = 2$, which is why oddness is assumed.
-- source:
--   Formal Conjectures library (Google DeepMind), Apache-2.0, https://github.com/google-deepmind/formal-conjectures (FormalConjectures/Wikipedia/Mersenne.lean); https://en.wikipedia.org/wiki/Mersenne_conjectures

import Mathlib
import Definitions.Def_FCP_Mersenne

namespace FCP.Mersenne

theorem new_mersenne_conjecture (p : ℕ) (hp : Odd p) : NewMersenneStatement p := by sorry

end FCP.Mersenne
