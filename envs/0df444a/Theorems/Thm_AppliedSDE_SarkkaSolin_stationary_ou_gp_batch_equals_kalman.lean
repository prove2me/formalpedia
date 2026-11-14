-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_stationary_ou_gp_batch_equals_kalman
-- name    : AppliedSDE.SarkkaSolin.stationary_ou_gp_batch_equals_kalman
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T17:46:15.207042+00:00
-- url     : https://prove2.me/theorems/b005e2e3-7db8-49d7-975f-8d9aaaedb8b2
-- title:
--   OU Gaussian-process batch regression agrees with sequential Kalman filtering
-- statement:
--   Capstone, drawing on Särkkä and Solin (2019) Chapters 6, 10 and 12. Sample a mean-zero stationary scalar Ornstein–Uhlenbeck process with rate λ>0 and diffusion variance q>0 at equally spaced times with spacing Δ>0. Let V=q/(2λ) and a=exp(-λΔ), so its finite covariance matrix is K_ij=V a^|i-j|. Given an observation vector y with independent observation-noise variance r>0, define the batch Gaussian-process posterior mean K(K+rI)^{-1}y. Define the scalar Kalman filtering mean and covariance by their usual first-observation update and then, for each subsequent observation, the OU prediction and noisy-observation update recurrences. The theorem asserts that the final Kalman filtering mean is exactly the final coordinate of the batch GP posterior mean. This is a multi-observation identity and does not assume either expression equals the other. Its Gaussian model and algebraic recurrences are explicit, and it remains distinct from full conditional-distribution or smoothing equivalence. The theorem now refers to the separately declared OU covariance, Kalman prediction/update and batch GP interface operations.
--
--   Representative mathematical statement, subject to the precise formal hypotheses:
--
--   $$
--   m^{\mathrm{KF}}_n=e_n^\top K(K+rI)^{-1}y
--   $$
-- source:
--   Original derived capstone from Simo Särkkä and Arno Solin, Applied Stochastic Differential Equations (Cambridge University Press, 2019): Example 6.2, scalar Ornstein–Uhlenbeck transition, printed pp. 80–81; Algorithm 10.18, discrete Kalman filter, printed p. 216; Section 12.2, noisy GP posterior formula (12.13)–(12.14), printed p. 255; Section 12.4, GP regression via Kalman filtering, printed pp. 265–268. This new multi-observation equality is synthesised from these results and is not claimed to be a verbatim numbered textbook theorem. https://doi.org/10.1017/9781108186735

import Mathlib
import Definitions.Def_AppliedSDE_SarkkaSolin_OUKalmanInterfaces
open Matrix
open scoped BigOperators Matrix

theorem AppliedSDE.SarkkaSolin.stationary_ou_gp_batch_equals_kalman
    (n : ℕ) (rate q Δ r : ℝ)
    (hrate : 0 < rate) (hq : 0 < q) (hΔ : 0 < Δ) (hr : 0 < r)
    (y : Fin (n + 1) → ℝ) (m P : Fin (n + 1) → ℝ) :
    let V : ℝ := q / (2 * rate)
    let a : ℝ := AppliedSDE.SarkkaSolin.ouStepFactor rate Δ
    let K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
      fun i j => AppliedSDE.SarkkaSolin.stationaryOUCovariance rate q ((i.val : ℝ) * Δ) ((j.val : ℝ) * Δ)
    (P 0 = V * r / (V + r)) →
    (m 0 = V / (V + r) * y 0) →
    (∀ k : Fin n,
      let predicted : ℝ := AppliedSDE.SarkkaSolin.ouPredictedVariance rate q Δ (P k.castSucc)
      P k.succ = AppliedSDE.SarkkaSolin.scalarUpdatedVariance predicted r ∧
      m k.succ = a * m k.castSucc +
        AppliedSDE.SarkkaSolin.scalarKalmanGain predicted r * (y k.succ - a * m k.castSucc)) →
    m (Fin.last n) =
      AppliedSDE.SarkkaSolin.gpBatchPosteriorMean K r y
        (Fin.last n) := by
  sorry
