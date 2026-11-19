-- Prove2me | Theorems.Thm_ECDLP_p_prime
-- name    : ECDLP.p_prime
-- status  : Proved
-- author  : @LG
-- created : 2026-11-16T23:42:48.043452+00:00
-- url     : https://prove2.me/theorems/882dfcf6-0bfe-494d-8488-4e024ac08c21
-- title:
--   The challenge modulus $p$ is prime
-- statement:
--   The modulus of the FrontierMath ECDLP challenge,
--
--   $$p = 92031864238688105485400538143121826382268912998421731683072033206257804487869,$$
--
--   is a prime number. The benchmark presents $p$ as a 256-bit prime; this theorem certifies that assertion. It provides the `Fact (Nat.Prime ECDLP.p)` instance under which $\mathbb{F}_p = \mathbb{Z}/p\mathbb{Z}$ is a field and the elliptic-curve group law on $E(\mathbb{F}_p)$ is available.
--
--   **Formalization Note.** The statement is `Nat.Prime` applied to the concrete natural number `ECDLP.p` from the challenge-data definition.
-- source:
--   Epoch AI, FrontierMath: Open Problems — The Elliptic-Curve Discrete Logarithm Problem (ECDLP), https://epoch.ai/frontiermath/open-problems/elliptic-curve-discrete-logarithm — public challenge data (p, a, b, P, Q, n, h) and Task section.

import Mathlib
import Definitions.Def_ECDLPChallengeData

namespace ECDLP

theorem p_prime : Nat.Prime ECDLP.p := by sorry

end ECDLP
