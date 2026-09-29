-- Prove2me | Theorems.Thm_EulerMascheroni_P2_factorial_binomial_identity
-- name    : EulerMascheroni.P2.factorial_binomial_identity
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-12T19:44:23.16693+00:00
-- url     : https://prove2.me/theorems/08be2964-7e1e-41c1-a71e-a384e5e86391
-- title:
--   The P2 denominator as a factorial-weighted integer sum
-- statement:
--   For every integer $n\ge0$, the rational denominator sum of the P2 approximation satisfies the exact identity
--
--   $$n!Q_n=\sum_{j=0}^n j!\binom nj^3\binom{2n-j}{n}^{\!2}.$$
--
--   Thus $n!Q_n$ is a nonnegative integer represented by a factorial-weighted binomial sum. This connects the original approximation coefficients to modular truncation: whenever $q\mid J!$, terms with $j\ge J$ vanish modulo $q$.
-- source:
--   Derived auxiliary results for the p=2, x=1 family in Van Assche–Wolfs, Rational approximation of Euler’s constant using multiple orthogonal polynomials, arXiv:2404.09799v3, Section 5, displayed binomial formula for F_(n;2)^(I|p), https://arxiv.org/html/2404.09799v3#S5. The reduced-fraction normalization and conditional subsequence criterion are elementary deductions supplied here, not named statements or arithmetic-saving claims in that paper.

import Definitions.Def_eulerMascheroni_p2Approximation
open scoped BigOperators
open EulerMascheroni.P2

theorem EulerMascheroni.P2.factorial_binomial_identity (n : ℕ) : (n.factorial : ℚ) * Q n =
    ((∑ j ∈ Finset.range (n+1),
      j.factorial * (n.choose j)^3 * ((2*n-j).choose n)^2 : ℕ) : ℚ)  := by sorry
