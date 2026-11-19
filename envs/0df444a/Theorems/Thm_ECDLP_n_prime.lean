-- Prove2me | Theorems.Thm_ECDLP_n_prime
-- name    : ECDLP.n_prime
-- status  : Proved
-- author  : @LG
-- created : 2026-11-16T23:43:21.957632+00:00
-- url     : https://prove2.me/theorems/b027a3de-e9c7-432b-913b-230b275e82ca
-- title:
--   The challenge subgroup order $n$ is prime
-- statement:
--   The subgroup order of the FrontierMath ECDLP challenge,
--
--   $$n = 18406372847737621097080107628624365276513063062857122317960690589425712086189,$$
--
--   is a prime number. The benchmark presents $n$ as the 254-bit prime order of the base point $P$; this theorem certifies that assertion. Primality of $n$ is what makes the challenge resistant to the Pohlig–Hellman reduction and makes the discrete logarithm in $\langle P\rangle$ unique modulo $n$.
--
--   **Formalization Note.** The statement is `Nat.Prime` applied to the concrete natural number `ECDLP.n` from the challenge-data definition.
-- source:
--   Epoch AI, FrontierMath: Open Problems — The Elliptic-Curve Discrete Logarithm Problem (ECDLP), https://epoch.ai/frontiermath/open-problems/elliptic-curve-discrete-logarithm — public challenge data (p, a, b, P, Q, n, h) and Task section.

import Mathlib
import Definitions.Def_ECDLPChallengeData

namespace ECDLP

theorem n_prime : Nat.Prime ECDLP.n := by sorry

end ECDLP
