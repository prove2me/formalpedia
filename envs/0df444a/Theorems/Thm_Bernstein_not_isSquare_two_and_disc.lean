-- Prove2me | Theorems.Thm_Bernstein_not_isSquare_two_and_disc
-- name    : Bernstein.not_isSquare_two_and_disc
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-22T17:15:37.430594+00:00
-- url     : https://prove2.me/theorems/f5928956-25c7-48fb-882e-542e4226effc
-- title:
--   §2 — 2 and 486662² − 4 are not squares modulo 2^255 − 19
-- statement:
--   In $\mathbf{F}_p$ with $p = 2^{255} - 19$, $2$ is not a square, so $\mathbf{F}_p[\sqrt{2}] = \mathbf{F}_p[X]/(X^2 - 2)$ is a field; and $486662^2 - 4$ is not a square.
-- source:
--   Bernstein, D. J., Curve25519: new Diffie-Hellman speed records, in: Public Key Cryptography – PKC 2006, Lecture Notes in Computer Science 3958, Springer, 2006, 207–228, https://doi.org/10.1007/11745853_14 (author's version of 2006-02-09: https://cr.yp.to/ecdh/curve25519-20060209.pdf), p. 4, §2, 2 and 486662² − 4 are not squares

import Mathlib
import Definitions.Def_Curve25519Bernstein

namespace Bernstein

theorem not_isSquare_two_and_disc :
    ¬ IsSquare (2 : ZMod p25519) ∧
    IsField (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C (2 : ZMod p25519))) ∧
    ¬ IsSquare ((A25519 : ZMod p25519) ^ 2 - 4) := by
  sorry

end Bernstein
