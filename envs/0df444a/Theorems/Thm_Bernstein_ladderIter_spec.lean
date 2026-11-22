-- Prove2me | Theorems.Thm_Bernstein_ladderIter_spec
-- name    : Bernstein.ladderIter_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-22T17:16:18.107969+00:00
-- url     : https://prove2.me/theorems/e659d117-68b5-4478-bc51-260e3c2a76ee
-- title:
--   §5 — k double-and-add steps take X(⌊n/2^k⌋Q) to X(nQ)
-- statement:
--   Assume $p = 2^{255} - 19$ is prime, and let $E$ be $y^2 = x^3 + 486662x^2 + x$. Let $q \in \mathbf{F}_p$ be nonzero and $Q \in E(\mathbf{F}_{p^2})$ with $X(Q) = q$. Let $n, k \ge 0$, and let $(x, z) \neq (0, 0)$ and $(x', z') \neq (0, 0)$ be fractions over $\mathbf{F}_p$ with $x/z = X(\lfloor n/2^k \rfloor Q)$ and $x'/z' = X(\lfloor n/2^k \rfloor Q + Q)$. Apply $k$ steps of the double-and-add procedure, for bits $k - 1, \ldots, 0$ of $n$, each step doubling one fraction by Theorem B.1's formula (with $(A - 2)/4 = 121665$) and adding the two by Theorem B.2's formula (with $x_1 = q$, $z_1 = 1$). The resulting fractions are not $(0, 0)$, and they are $X(nQ)$ and $X(nQ + Q)$.
-- source:
--   Bernstein, D. J., Curve25519: new Diffie-Hellman speed records, in: Public Key Cryptography – PKC 2006, Lecture Notes in Computer Science 3958, Springer, 2006, 207–228, https://doi.org/10.1007/11745853_14 (author's version of 2006-02-09: https://cr.yp.to/ecdh/curve25519-20060209.pdf), pp. 13–14, §5, Scalar multiplication (the formulas repeated k times)

import Mathlib
import Definitions.Def_Curve25519Bernstein

namespace Bernstein

theorem ladderIter_spec [Fact p25519.Prime] (q : ZMod p25519) (hq : q ≠ 0)
    (Q : Pt p25519 A25519) (hQ : X Q = some (emb p25519 q)) (n k : ℕ)
    (x z x' z' : ZMod p25519) (hxz : (x, z) ≠ (0, 0)) (hxz' : (x', z') ≠ (0, 0))
    (h : frac x z = X (((n / 2 ^ k : ℕ) : ℤ) • Q))
    (h' : frac x' z' = X (((n / 2 ^ k : ℕ) : ℤ) • Q + Q)) :
    let st := ladderIter (121665 : ZMod p25519) q n k (x, z, x', z')
    (st.1, st.2.1) ≠ (0, 0) ∧ (st.2.2.1, st.2.2.2) ≠ (0, 0) ∧
      frac st.1 st.2.1 = X ((n : ℤ) • Q) ∧ frac st.2.2.1 st.2.2.2 = X ((n : ℤ) • Q + Q) := by
  sorry

end Bernstein
