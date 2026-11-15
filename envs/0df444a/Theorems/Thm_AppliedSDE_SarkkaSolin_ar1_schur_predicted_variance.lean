-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_schur_predicted_variance
-- name    : AppliedSDE.SarkkaSolin.ar1_schur_predicted_variance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:53:44.89952+00:00
-- url     : https://prove2.me/theorems/bedff572-4870-4279-a925-b1f002009fbd
-- title:
--   Schur predictive conditional variance identity for an AR(1) covariance extension
-- statement:
--   Suppose the posterior variance of a Gaussian-process state is P=V-k dot A k, where V is its stationary variance, k its observation cross-covariance vector and A the inverse old observation covariance matrix. If the next-state cross-covariance is a k, its conditional variance is V-(a k) dot A (a k)=a²P+V(1-a²). This is the exact Schur-complement predictive variance identity required for the batch GP equals sequential Kalman filtering induction at arbitrary sample size.
-- source:
--   Särkkä and Solin (2019), Applied Stochastic Differential Equations, Chapters 10 and 12; conditional Gaussian Schur complement and stationary AR(1) prediction.

import Mathlib
open Matrix
open scoped Matrix

theorem AppliedSDE.SarkkaSolin.ar1_schur_predicted_variance
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (k : Fin n → ℝ) (a V P : ℝ)
    (hP : P = V - (k ⬝ᵥ A.mulVec k)) :
    V - ((a • k) ⬝ᵥ A.mulVec (a • k)) =
      a ^ 2 * P + V * (1 - a ^ 2) := by
  sorry
