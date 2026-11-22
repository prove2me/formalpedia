-- Prove2me | Theorems.Thm_Bernstein_curve25519_spec
-- name    : Bernstein.curve25519_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-22T17:15:56.200837+00:00
-- url     : https://prove2.me/theorems/c77d5b67-a7a8-493e-b878-a19b8f5a348f
-- title:
--   §2 — The Curve25519 function is well defined
-- statement:
--   Assume $p = 2^{255} - 19$ is prime, and let $E$ be $y^2 = x^3 + 486662x^2 + x$. Then:
--   - the little-endian encoding $s \mapsto \underline{s}$ and its inverse are mutually inverse bijections between $\{0, 1, \ldots, 2^{256} - 1\}$ and the 32-byte strings;
--   - a 32-byte string lies in $\{0, 8, \ldots, 248\} \times \{0, \ldots, 255\}^{30} \times \{64, \ldots, 127\}$ exactly when the integer it encodes lies in $2^{254} + 8\{0, 1, \ldots, 2^{251} - 1\}$;
--   - for every $n \in 2^{254} + 8\{0, 1, \ldots, 2^{251} - 1\}$ and $q \in \{0, 1, \ldots, 2^{256} - 1\}$ there is exactly one integer $s \in \{0, 1, \ldots, 2^{255} - 20\}$ with $s = X_0(nQ)$ for all $Q \in E(\mathbf{F}_{p^2})$ such that $X_0(Q) = q \bmod p$; $\mathrm{Curve25519}(n, q)$ is this $s$; and the last byte of $\mathrm{Curve25519}(\underline{n}, \underline{q})$ is below $128$, that is, its final bit is $0$;
--   - for every secret key $b$ and every public key $c$ (as 32-byte strings) the last byte of $\mathrm{Curve25519}(b, c)$ is below $128$, so $\mathrm{Curve25519}$ is not surjective onto the 32-byte strings.
-- source:
--   Bernstein, D. J., Curve25519: new Diffie-Hellman speed records, in: Public Key Cryptography – PKC 2006, Lecture Notes in Computer Science 3958, Springer, 2006, 207–228, https://doi.org/10.1007/11745853_14 (author's version of 2006-02-09: https://cr.yp.to/ecdh/curve25519-20060209.pdf), pp. 4–5, §2, the Curve25519 function is well defined

import Mathlib
import Definitions.Def_Curve25519Bernstein

namespace Bernstein

theorem curve25519_spec [Fact p25519.Prime] :
    (∀ s : ℕ, s < 2 ^ 256 → ofBytes (bytes s) = s) ∧
    (∀ b : Fin 32 → Fin 256, ofBytes b < 2 ^ 256 ∧ bytes (ofBytes b) = b) ∧
    (∀ b : Fin 32 → Fin 256, b ∈ secretKeyBytes ↔ ofBytes b ∈ secretKeys) ∧
    (∀ n q : ℕ, n ∈ secretKeys → q < 2 ^ 256 →
      (∃! s : ℕ, s ≤ 2 ^ 255 - 20 ∧
        ∀ Q : Pt p25519 A25519, X0 Q = emb p25519 (q : ZMod p25519) →
          X0 ((n : ℤ) • Q) = emb p25519 (s : ZMod p25519)) ∧
      curve25519 n q ≤ 2 ^ 255 - 20 ∧
      (∀ Q : Pt p25519 A25519, X0 Q = emb p25519 (q : ZMod p25519) →
        X0 ((n : ℤ) • Q) = emb p25519 (curve25519 n q : ZMod p25519)) ∧
      ((curve25519Bytes (bytes n) (bytes q) 31 : ℕ) < 128)) ∧
    (∀ b c : Fin 32 → Fin 256, b ∈ secretKeyBytes → (curve25519Bytes b c 31 : ℕ) < 128) ∧
    ¬ ∀ d : Fin 32 → Fin 256, ∃ b c : Fin 32 → Fin 256, b ∈ secretKeyBytes ∧
      curve25519Bytes b c = d := by
  sorry

end Bernstein
