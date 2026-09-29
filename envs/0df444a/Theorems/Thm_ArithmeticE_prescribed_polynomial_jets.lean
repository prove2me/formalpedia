-- Prove2me | Theorems.Thm_ArithmeticE_prescribed_polynomial_jets
-- name    : ArithmeticE.prescribed_polynomial_jets
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T16:37:36.161516+00:00
-- url     : https://prove2.me/theorems/6582df00-7d8d-46b4-864b-18e5a2394f7d
-- title:
--   Finite polynomial derivative interpolation at an arbitrary point
-- statement:
--   Over a field $K$ of characteristic zero, any finite list of derivative values can be prescribed at a point $\xi\in K$. For any sequence $a_k\in K$ and integer $N\ge0$, there is a polynomial $P$ such that $P^{(k)}(\xi)=a_k$ for all $k<N$. A witness is the finite Taylor polynomial $\sum_{k<N}a_k(X-\xi)^k/k!$. This supplies the polynomial interpolation ingredient used to choose the derivative rows in the ordinary cyclic-vector construction. It does not itself construct the covariant derivative rows or prove scalar-equation minimality.
-- source:
--   Finite Taylor interpolation; used in Beukers, https://webspace.science.uu.nl/~beuke106/siegelshidlovskii.pdf, Theorem 3.2, pp. 6–7.

import Mathlib

theorem ArithmeticE.prescribed_polynomial_jets {K : Type*} [Field K] [CharZero K]
    (ξ : K) (N : ℕ) (a : ℕ → K) :
    ∃ P : Polynomial K, ∀ k < N, (Polynomial.derivative^[k] P).eval ξ = a k := by sorry
