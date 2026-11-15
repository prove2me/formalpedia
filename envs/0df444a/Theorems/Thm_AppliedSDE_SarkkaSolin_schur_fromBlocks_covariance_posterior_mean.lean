-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_schur_fromBlocks_covariance_posterior_mean
-- name    : AppliedSDE.SarkkaSolin.schur_fromBlocks_covariance_posterior_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T13:46:00.131848+00:00
-- url     : https://prove2.me/theorems/544b2ab2-9199-458e-a028-3c308b0817c2
-- title:
--   Posterior mean as final observation minus noise-weighted Schur innovation
-- statement:
--   In a finite symmetric noisy covariance block system with final diagonal V+r and cross covariance b, solve the block equations C z = y. The associated covariance-weighted final posterior mean b dot z_old + V*z_last equals y_last minus r times the Schur-normalised innovation (y_last-b dot A y_old)/(V+r-b dot A b). This is the exact generic matrix step needed to connect the batch Gaussian-process mean with the Kalman innovation recurrence.
-- source:
--   Sarkka and Solin (2019), Applied Stochastic Differential Equations, GP conditioning and Kalman recursions, Chapters 10 and 12.

import Mathlib
open Matrix
open scoped Matrix

theorem AppliedSDE.SarkkaSolin.schur_fromBlocks_covariance_posterior_mean
    (n : ℕ) (M A : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n -> ℝ) (V r : ℝ)
    (y z : Fin n ⊕ Fin 1 -> ℝ)
    (hAM : A * M = 1)
    (hblock :
      (Matrix.fromBlocks M
        (fun i (_ : Fin 1) => b i )
        (fun (_ : Fin 1) j => b j )
        (fun (_ _ : Fin 1) => V + r )).mulVec z = y)
    (hS : (V + r) - (b ⬝ᵥ A.mulVec b) ≠ 0) :
    (b ⬝ᵥ (z ∘ Sum.inl)) + V * z (Sum.inr (0 : Fin 1)) =
      y (Sum.inr (0 : Fin 1)) -
        r * ((y (Sum.inr (0 : Fin 1)) -
          (b ⬝ᵥ A.mulVec (y ∘ Sum.inl))) /
          ((V + r) - (b ⬝ᵥ A.mulVec b))) := by
  sorry
