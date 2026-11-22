-- Prove2me | Theorems.Thm_Bernstein_theorem_2_1
-- name    : Bernstein.theorem_2_1
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-22T17:16:55.664508+00:00
-- url     : https://prove2.me/theorems/4d8c7829-892b-4b04-a0f7-15561b721738
-- title:
--   Theorem 2.1 — X₀(nQ) depends only on X₀(Q), and lies in F_p
-- statement:
--   Let $p \ge 5$ be prime and $A$ an integer such that $A^2 - 4$ is not a square modulo $p$. Let $E$ be the curve $y^2 = x^3 + Ax^2 + x$ over $\mathbf{F}_p$ and $E(\mathbf{F}_{p^2})$ its group of points over $\mathbf{F}_{p^2}$, and let $X_0(\infty) = 0$, $X_0(x, y) = x$. Then for every integer $n$ and every $q \in \mathbf{F}_p$ there is exactly one $s \in \mathbf{F}_p$ such that $X_0(nQ) = s$ for all $Q \in E(\mathbf{F}_{p^2})$ with $X_0(Q) = q$.
--
--   Bernstein, p. 4: “**Theorem 2.1.** Let $p$ be a prime number with $p \ge 5$. Let $A$ be an integer such that $A^2 - 4$ is not a square modulo $p$. Define $E$ as the elliptic curve $y^2 = x^3 + Ax^2 + x$ over the field $\mathbf{F}_p$. Define $X_0 : E(\mathbf{F}_{p^2}) \to \mathbf{F}_{p^2}$ as follows: $X_0(\infty) = 0$; $X_0(x, y) = x$. Let $n$ be an integer. Let $q$ be an element of $\mathbf{F}_p$. Then there exists a unique $s \in \mathbf{F}_p$ such that $X_0(nQ) = s$ for all $Q \in E(\mathbf{F}_{p^2})$ such that $X_0(Q) = q$.”
--
--   $\mathbf{F}_p$ sits inside $\mathbf{F}_{p^2}$ (Mathlib's `GaloisField p 2`) through `emb p`. Uniqueness is not vacuous: every $q \in \mathbf{F}_p$ is $X_0(Q)$ for some $Q$, since $q^3 + Aq^2 + q$ has a square root in $\mathbf{F}_{p^2}$.
-- source:
--   Bernstein, D. J., Curve25519: new Diffie-Hellman speed records, in: Public Key Cryptography – PKC 2006, Lecture Notes in Computer Science 3958, Springer, 2006, 207–228, https://doi.org/10.1007/11745853_14 (author's version of 2006-02-09: https://cr.yp.to/ecdh/curve25519-20060209.pdf), p. 4, Theorem 2.1

import Mathlib
import Definitions.Def_Curve25519Bernstein

namespace Bernstein

theorem theorem_2_1 (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (A : ℤ)
    (hA : ¬ IsSquare ((A : ZMod p) ^ 2 - 4)) (n : ℤ) (q : ZMod p) :
    ∃! s : ZMod p, ∀ Q : Pt p A, X0 Q = emb p q → X0 (n • Q) = emb p s := by
  sorry

end Bernstein
