-- Prove2me | Theorems.Thm_ECDLP_dlog_unique
-- name    : ECDLP.dlog_unique
-- status  : Proved
-- author  : @LG
-- created : 2026-11-16T23:44:30.811988+00:00
-- url     : https://prove2.me/theorems/f84cf0ae-8331-498c-93d1-6bd528dda75a
-- title:
--   Uniqueness of the discrete logarithm below the order
-- statement:
--   Let $G$ be an additive commutative group and $P \in G$ an element of order $n$. If $a, b$ are natural numbers with $a < n$ and $b < n$ and
--
--   $$aP = bP,$$
--
--   then $a = b$. In other words, the discrete logarithm in the cyclic subgroup $\langle P\rangle$ is unique in the range $[0, n)$; applied to the challenge base point, this shows that the benchmark's secret $x$ with $1 \le x < n$ and $Q = xP$ is the unique such integer.
--
--   **Formalization Note.** The order is Mathlib's `addOrderOf`, and `a • P` is the additive-monoid scalar multiplication ($a$-fold addition). The statement is for arbitrary additive commutative groups, so it is reusable beyond the challenge instance.
-- source:
--   Well-definedness of the discrete logarithm in a cyclic subgroup; implicit in the Epoch AI problem statement ('the integer x with 1 <= x < n such that Q = xP'), https://epoch.ai/frontiermath/open-problems/elliptic-curve-discrete-logarithm; standard treatment: Washington, Elliptic Curves: Number Theory and Cryptography, 2nd ed., Chapman & Hall/CRC 2008, Chapter 5.

import Mathlib

namespace ECDLP

theorem dlog_unique {G : Type*} [AddCommGroup G] {P : G} {n : ℕ}
    (hP : addOrderOf P = n) {a b : ℕ} (ha : a < n) (hb : b < n)
    (h : a • P = b • P) : a = b := by sorry

end ECDLP
