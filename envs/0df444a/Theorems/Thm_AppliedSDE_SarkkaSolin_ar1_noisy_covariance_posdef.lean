-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_noisy_covariance_posdef
-- name    : AppliedSDE.SarkkaSolin.ar1_noisy_covariance_posdef
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T22:49:54.901259+00:00
-- url     : https://prove2.me/theorems/cb5154cb-c478-443f-982d-1b611c808a85
-- title:
--   Noisy stationary AR(1) covariance matrix is positive definite
-- statement:
--   For any positive rate, diffusion variance, observation spacing and observation-noise variance, the sampled OU covariance K_ij=V a^|i-j|, V=q/(2rate), a=exp(-rate Delta), has a strictly positive definite noisy observation matrix K+rI. Reuse the Proved OU grid-covariance identity and the Proved noisy OU covariance positivity theorem. This certifies invertibility of the matrix used by batch GP regression and the scalar AR1 Kalman posterior.
-- source:
--   Särkkä and Solin (2019), Applied Stochastic Differential Equations, Chapters 6, 10 and 12, https://doi.org/10.1017/9781108186735

import Mathlib
import Definitions.Def_AppliedSDE_SarkkaSolin_OUKalmanInterfaces
open Matrix
open scoped BigOperators

theorem AppliedSDE.SarkkaSolin.ar1_noisy_covariance_posdef
    (n : ℕ) (rate q Δ r : ℝ)
    (hrate : 0 < rate) (hq : 0 < q) (hΔ : 0 < Δ) (hr : 0 < r) :
    ((Matrix.of fun i j : Fin (n + 1) =>
        q / (2 * rate) *
          (AppliedSDE.SarkkaSolin.ouStepFactor rate Δ) ^ Nat.dist i.val j.val) +
      r • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)).PosDef := by
  sorry
