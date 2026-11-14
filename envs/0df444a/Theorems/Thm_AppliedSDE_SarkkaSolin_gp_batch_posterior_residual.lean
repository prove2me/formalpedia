-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_gp_batch_posterior_residual
-- name    : AppliedSDE.SarkkaSolin.gp_batch_posterior_residual
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:50:29.173062+00:00
-- url     : https://prove2.me/theorems/5a39d948-2b52-4936-871d-8d956d90814a
-- title:
--   Noisy Gaussian-process posterior mean equals observation minus weighted inverse residual
-- statement:
--   For an arbitrary real symmetric positive-definite regularised kernel matrix M=K+rI, the GP posterior mean K M^{-1} y equals the observation vector minus r M^{-1} y. Positive definiteness guarantees matrix invertibility. This supplies a reusable matrix-level relation for the AR(1) batch Gaussian-process versus recursive Kalman identity 1b230031-7f34-4971-8d05-2f91cf171bd9, and reuses the proved AR1 noisy covariance positive definiteness certificate.
-- source:
--   Särkkä and Solin (2019), Applied Stochastic Differential Equations, Chapter 12, GP state-space regression.

import Mathlib
open Matrix

theorem AppliedSDE.SarkkaSolin.gp_batch_posterior_residual
    {n : ℕ}
    (K : Matrix (Fin n) (Fin n) ℝ)
    (r : ℝ) (y : Fin n → ℝ)
    (hM : (K + r • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef) :
    K.mulVec (((K + r • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹).mulVec y) =
      y - r • (((K + r • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹).mulVec y) := by
  sorry
