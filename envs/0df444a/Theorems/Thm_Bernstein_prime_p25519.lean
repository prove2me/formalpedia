-- Prove2me | Theorems.Thm_Bernstein_prime_p25519
-- name    : Bernstein.prime_p25519
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-22T17:15:15.70667+00:00
-- url     : https://prove2.me/theorems/12d712ee-b256-4ead-ae81-b8a51c4cbcfc
-- title:
--   §2 — 2^255 − 19 is prime
-- statement:
--   The number $2^{255} - 19$ is prime.
-- source:
--   Bernstein, D. J., Curve25519: new Diffie-Hellman speed records, in: Public Key Cryptography – PKC 2006, Lecture Notes in Computer Science 3958, Springer, 2006, 207–228, https://doi.org/10.1007/11745853_14 (author's version of 2006-02-09: https://cr.yp.to/ecdh/curve25519-20060209.pdf), p. 4, §2, the prime 2^255 − 19

import Mathlib
import Definitions.Def_Curve25519Bernstein

namespace Bernstein

theorem prime_p25519 : Nat.Prime p25519 := by
  sorry

end Bernstein
