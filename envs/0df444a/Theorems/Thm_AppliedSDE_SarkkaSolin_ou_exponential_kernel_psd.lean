-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_ou_exponential_kernel_psd
-- name    : AppliedSDE.SarkkaSolin.ou_exponential_kernel_psd
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:49:22.887903+00:00
-- url     : https://prove2.me/theorems/854ffc5c-b393-4caf-abcf-61baddcde5b7
-- title:
--   Stationary OU exponential covariance is positive semidefinite
-- statement:
--   From Särkkä and Solin (2019), Example 6.8, eqs (6.73)–(6.75), printed p. 91; Section 12.3 discusses the exponential covariance as a stationary GP. For nonnegative stationary variance V and positive mean-reversion rate, the kernel V exp(-rate |s-t|) has a nonnegative quadratic form on every finite collection of times. This is a substantive covariance-validity statement required for the GP/Kalman capstone.
--
--   Representative mathematical statement, subject to the precise formal hypotheses:
--
--   $$
--   \sum_{i,j}a_ia_j V e^{-\lambda|t_i-t_j|}\geq0
--   $$
-- source:
--   Original derived from Simo Särkkä and Arno Solin, Applied Stochastic Differential Equations (Cambridge University Press, 2019), Example 6.8, equation (6.75), and Section 12.3, OU kernel PSD, printed pp. 91 and 256–260. https://doi.org/10.1017/9781108186735

import Mathlib
open scoped BigOperators

theorem AppliedSDE.SarkkaSolin.ou_exponential_kernel_psd
    (n : ℕ) (rate V : ℝ) (hrate : 0 < rate) (hV : 0 ≤ V)
    (t : Fin n → ℝ) (a : Fin n → ℝ) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n,
      a i * a j * (V * Real.exp (-rate * |t i - t j|)) := by
  sorry
