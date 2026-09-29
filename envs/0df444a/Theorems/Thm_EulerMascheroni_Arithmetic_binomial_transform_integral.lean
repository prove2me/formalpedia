-- Prove2me | Theorems.Thm_EulerMascheroni_Arithmetic_binomial_transform_integral
-- name    : EulerMascheroni.Arithmetic.binomial_transform_integral
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T14:11:22.47847+00:00
-- url     : https://prove2.me/theorems/085836f4-8040-4366-8905-29f3cd9a7531
-- title:
--   Integer binomial weights preserve common-denominator integrality
-- statement:
--   For the factorial quotient coefficients $q_k(a)$, suppose $d q_k(a)$ is an algebraic integer for $0\le k\le2n$, where $d\in\mathbb N$. Then
--
--   $$d T_n(q(a))=d\sum_{j=0}^n\binom nj\binom{n+j}n q_{n+j}(a)$$
--
--   is an algebraic integer. The assertion holds for every real $a$.
-- source:
--   Matala-aho–Zudilin, Euler’s factorial series and global relations, https://arxiv.org/html/1703.02633, Eqs. (10)–(11). The normalization and algebraic-norm argument are an elementary derivation for this decomposition; the arithmetic division conjecture is not assumed in the unconditional lemmas.

import Definitions.Def_eulerMascheroni_padeTransform
open Filter EulerMascheroni.Arithmetic
open scoped Topology

theorem EulerMascheroni.Arithmetic.binomial_transform_integral (a : ℝ) (n d : ℕ)
    (h : ∀ k : ℕ, k ≤ 2*n → IsIntegral ℤ ((d:ℝ)*quotientCoeff a k)) :
    IsIntegral ℤ ((d:ℝ)*binomialTransform (quotientCoeff a) n) := by sorry
