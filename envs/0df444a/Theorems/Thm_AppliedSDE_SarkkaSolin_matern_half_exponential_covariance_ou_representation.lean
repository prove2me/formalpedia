-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_matern_half_exponential_covariance_ou_representation
-- name    : AppliedSDE.SarkkaSolin.matern_half_exponential_covariance_ou_representation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:55:50.388187+00:00
-- url     : https://prove2.me/theorems/478f8201-2fca-4331-8072-6052b511d409
-- title:
--   Matérn one-half exponential covariance equals stationary OU covariance
-- statement:
--   Särkkä and Solin (2019), Section 12.3 and equation (12.33), identifies the Matérn ν=1/2 covariance with the exponential kernel and a stationary OU model. For positive length scale ℓ and positive GP variance v, choose the OU mean-reversion rate λ=1/ℓ and Brownian diffusion variance q=2v/ℓ. The stationary OU covariance then agrees exactly, at all pairs of times, with v exp(−|s−t|/ℓ). This is an exact covariance equivalence and establishes the parameter correspondence; equality of all Gaussian process finite-dimensional laws requires their Gaussian-law assumptions, a separate mathematical step.
--
--   Representative mathematical statement, subject to the precise formal hypotheses:
--
--   $$
--   v\,e^{-|s-t|/\ell}=\frac{q}{2\lambda}e^{-\lambda|s-t|},\quad\lambda=\ell^{-1},\ q=2v/\ell
--   $$
-- source:
--   Original derived from Simo Särkkä and Arno Solin, Applied Stochastic Differential Equations (Cambridge University Press, 2019), Section 12.3, equation (12.33) and the Matérn ν=1/2 special case, printed pp. 257–260. https://doi.org/10.1017/9781108186735

import Mathlib
import Definitions.Def_AppliedSDE_SarkkaSolin_OUKalmanInterfaces

theorem AppliedSDE.SarkkaSolin.matern_half_exponential_covariance_ou_representation
    (length variance s t : ℝ)
    (hlength : 0 < length) (hvariance : 0 < variance) :
    AppliedSDE.SarkkaSolin.stationaryOUCovariance
        (1 / length) (2 * variance / length) s t =
      variance * Real.exp (-|s - t| / length) := by
  sorry
