-- Prove2me | Theorems.Thm_Bernstein_ladder_eq_curve25519
-- name    : Bernstein.ladder_eq_curve25519
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-22T17:16:38.878541+00:00
-- url     : https://prove2.me/theorems/c2ffc75c-18df-42a2-a912-ae52fd6a6480
-- title:
--   §5 — The 255-step ladder computes Curve25519
-- statement:
--   Assume $p = 2^{255} - 19$ is prime, let $E$ be $y^2 = x^3 + 486662x^2 + x$, and let $n \in 2^{254} + 8\{0, 1, \ldots, 2^{251} - 1\}$. For $q \in \mathbf{F}_p$, let $\mathrm{ladder}(n, q) = xz^{p-2}$, where $x/z$ is the first fraction produced by 255 double-and-add steps on the bits of $n$ (as in the previous milestone, with $x_1 = q$) starting from $X(0) = 1/0$ and $X(Q) = q/1$. Then:
--   - $X_0(nQ) = \mathrm{ladder}(n, q)$ for every $q \in \mathbf{F}_p$ and every $Q \in E(\mathbf{F}_{p^2})$ with $X_0(Q) = q$, including $q = 0$;
--   - for $q \neq 0$, the final fraction $x/z$ is not $(0, 0)$ and is $X(nQ)$ (with $x/0 = \infty$);
--   - for $q = 0$, after at least one step both denominators are $0$;
--   - for every integer $q \in \{0, 1, \ldots, 2^{256} - 1\}$, $\mathrm{Curve25519}(n, q)$ equals $\mathrm{ladder}(n, q \bmod p)$ as an integer in $\{0, \ldots, p - 1\}$.
-- source:
--   Bernstein, D. J., Curve25519: new Diffie-Hellman speed records, in: Public Key Cryptography – PKC 2006, Lecture Notes in Computer Science 3958, Springer, 2006, 207–228, https://doi.org/10.1007/11745853_14 (author's version of 2006-02-09: https://cr.yp.to/ecdh/curve25519-20060209.pdf), p. 14, §5, Scalar multiplication (computing Curve25519)

import Mathlib
import Definitions.Def_Curve25519Bernstein

namespace Bernstein

theorem ladder_eq_curve25519 [Fact p25519.Prime] (n : ℕ) (hn : n ∈ secretKeys) :
    (∀ (q : ZMod p25519) (Q : Pt p25519 A25519), X0 Q = emb p25519 q →
      X0 ((n : ℤ) • Q) = emb p25519 (ladder n q)) ∧
    (∀ (q : ZMod p25519) (Q : Pt p25519 A25519), q ≠ 0 → X0 Q = emb p25519 q →
      let st := ladderIter (121665 : ZMod p25519) q n 255 (1, 0, q, 1)
      (st.1, st.2.1) ≠ (0, 0) ∧ frac st.1 st.2.1 = X ((n : ℤ) • Q)) ∧
    (∀ k : ℕ, 1 ≤ k →
      (ladderIter (121665 : ZMod p25519) 0 n k (1, 0, 0, 1)).2.1 = 0 ∧
      (ladderIter (121665 : ZMod p25519) 0 n k (1, 0, 0, 1)).2.2.2 = 0) ∧
    (∀ q : ℕ, q < 2 ^ 256 → curve25519 n q = (ladder n (q : ZMod p25519)).val) := by
  sorry

end Bernstein
