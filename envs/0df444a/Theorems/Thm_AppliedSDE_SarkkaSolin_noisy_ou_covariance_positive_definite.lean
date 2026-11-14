-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_noisy_ou_covariance_positive_definite
-- name    : AppliedSDE.SarkkaSolin.noisy_ou_covariance_positive_definite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:49:36.235381+00:00
-- url     : https://prove2.me/theorems/aa90839a-2289-4730-84ec-26aaab3c49fe
-- title:
--   OU covariance plus independent Gaussian observation noise is positive definite
-- statement:
--   Särkkä and Solin (2019), Example 6.8, eq (6.75), and Section 12.2 noisy Gaussian-process posterior, eqs (12.13)–(12.14). Assume stationary OU covariance V exp(-rate |ti-tj|), positive observation noise variance r, and a nonzero weights vector. The covariance quadratic form including r on the diagonal is strictly positive. This establishes nonsingularity of the covariance matrix needed by the batch GP regression formula; in the full proof the OU kernel PSD is a dependency.
--
--   Representative mathematical statement, subject to the precise formal hypotheses:
--
--   $$
--   a^\top(K+rI)a\geq r\,\lVert a\rVert^2>0\quad(a\neq0)
--   $$
-- source:
--   Original derived from Simo Särkkä and Arno Solin, Applied Stochastic Differential Equations (Cambridge University Press, 2019), Example 6.8 and Section 12.2, noisy OU covariance matrix, printed pp. 91 and 255–256. https://doi.org/10.1017/9781108186735

import Mathlib
open scoped BigOperators

theorem AppliedSDE.SarkkaSolin.noisy_ou_covariance_positive_definite
    (n : ℕ) (rate V r : ℝ) (hrate : 0 < rate) (hV : 0 ≤ V)
    (hr : 0 < r) (t : Fin n → ℝ) (a : Fin n → ℝ)
    (ha : a ≠ 0) :
    0 < ∑ i : Fin n, ∑ j : Fin n,
      a i * a j * (
        V * Real.exp (-rate * |t i - t j|) +
          if i = j then r else 0) := by
  sorry
