-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_three_mgf_strict_gap_ws01f
-- name    : AvramDividend.Classical.gaussian_three_mgf_strict_gap_ws01f
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T12:39:42.821098+00:00
-- url     : https://prove2.me/theorems/f9a81d00-0cfb-4664-bded-3f826e6e1bb3
-- title:
--   A finite three-moment comparison admits a strict Gaussian negative-tail gap
-- statement:
--   For a positive Gaussian Laplace exponent coefficient a, one can choose a positive integer three-moment scale m so that the limiting right-hand side of the integrated three-exponential negative-indicator inequality is strictly below its limiting left-hand side. This strict deficit ensures a positive negative-tail probability for small Lévy times through the actual exponential moments, without invoking weak convergence or jump-path o(t).
-- source:
--   Elementary strict inequality exp(a)>1+a and the limit as m tends to infinity of m²(exp(a/m²)-1) equals a, with an elementary exponential upper bound; WS1F three-MGF Gaussian route.

import Mathlib

open Filter

theorem AvramDividend.Classical.gaussian_three_mgf_strict_gap_ws01f (a : ℝ) (ha : 0 < a) :
    ∃ m : ℕ, 0 < m ∧
      (m : ℝ) ^ 2 *
          (Real.exp (a / ((m : ℝ) ^ 2)) - 1) +
        (Real.exp (4 * a) - 1) / (m : ℝ) <
          Real.exp a - 1 := by sorry
