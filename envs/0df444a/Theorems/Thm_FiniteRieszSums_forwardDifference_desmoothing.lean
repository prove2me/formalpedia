-- Prove2me | Theorems.Thm_FiniteRieszSums_forwardDifference_desmoothing
-- name    : FiniteRieszSums.forwardDifference_desmoothing
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T00:26:08.096214+00:00
-- url     : https://prove2.me/theorems/60f0c008-47ab-4eff-8db7-3f6e9fa3f4c3
-- title:
--   Recovering a sharp sum from finite differences of its Riesz sums
-- statement:
--   Let $a(n)$ be a complex sequence with $|a(n)|\le 1$, let $S(x)=\sum_{n\le x}a(n)$ and set $R_m(t)=\sum_{n\le t}a(n)(t-n)^m$ at nonnegative integers. For every integer order $m\ge0$, positive integer spacing $h$, and integer $x\ge0$, the $m$-fold forward difference $\Delta_h^m$ satisfies
--   $$\left|\Delta_h^m R_m(x)-m!h^m S(x)\right|\le 2^m(mh)^{m+1}.$$
--   For fixed $m\ge1$, division by $m!h^m$ recovers the sharp sum with error $O_m(h)$. This estimate applies to the coefficients $a(n)=\mu(n)\chi(n)$ used in the mission's sharp twisted Möbius bound.
-- source:
--   Independent elementary derivation for the finite Riesz kernel, using Mathlib’s forward-difference formula and its evaluation on a monomial: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Group/ForwardDiff.lean. For the corresponding analytic Perron kernel see the Perron–Mellin formula, Theorem 7.6, equation (7.52), https://www.cs.purdue.edu/homes/spa/courses/pg17/mybook.pdf.

import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Analysis.Complex.Basic

theorem FiniteRieszSums.forwardDifference_desmoothing (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (m x h : ℕ) (hh : 0 < h) :
    let R := fun t : ℕ => ∑ n ∈ Finset.range (t+1), a n * ((t:ℂ)-n)^m
    let S := ∑ n ∈ Finset.range (x+1), a n
    ‖(fwdDiff h)^[m] R x - ((m.factorial:ℂ)*(h:ℂ)^m)*S‖ ≤
      (2:ℝ)^m * ((m:ℝ)*h)^(m+1) := by sorry
