-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_stationary_ou_covariance_grid_equals_ar_power
-- name    : AppliedSDE.SarkkaSolin.stationary_ou_covariance_grid_equals_ar_power
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:51:17.003722+00:00
-- url     : https://prove2.me/theorems/b9c2bf08-5edb-4a03-93af-04d8e8892d44
-- title:
--   Stationary OU covariance on an equally spaced grid equals AR(1) matrix powers
-- statement:
--   Derived from Särkkä and Solin (2019), Example 6.8, equation (6.75), and the exact state transition in Chapter 6. For a positive mean-reversion rate and positive step length, the continuous-time stationary OU kernel at grid points iΔ and jΔ equals the stationary variance times a to the integer distance |i−j|, where a=exp(−rate Δ). This algebraically links the covariance of the SDE to the Toeplitz matrix used by the Gaussian-process regression and Kalman capstone; it requires the source-backed OU kernel and OU step-factor definitions.
--
--   Representative mathematical statement, subject to the precise formal hypotheses:
--
--   $$
--   K(i\Delta,j\Delta)=V a^{|i-j|},\qquad a=e^{-\lambda\Delta}
--   $$
-- source:
--   Original derived from Simo Särkkä and Arno Solin, Applied Stochastic Differential Equations (Cambridge University Press, 2019), Example 6.8, equation (6.75), printed p. 91, and Chapter 6 exact linear SDE discretisation. https://doi.org/10.1017/9781108186735

import Mathlib
import Definitions.Def_AppliedSDE_SarkkaSolin_OUKalmanInterfaces
open scoped BigOperators

theorem AppliedSDE.SarkkaSolin.stationary_ou_covariance_grid_equals_ar_power
    (rate q Δ : ℝ) (hrate : 0 < rate) (hΔ : 0 < Δ)
    (i j : ℕ) :
    AppliedSDE.SarkkaSolin.stationaryOUCovariance rate q
        (i * Δ) (j * Δ) =
      q / (2 * rate) *
        (AppliedSDE.SarkkaSolin.ouStepFactor rate Δ) ^ Nat.dist i j := by
  sorry
