-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_schur_linear_system_to_kalman_mean
-- name    : AppliedSDE.SarkkaSolin.schur_linear_system_to_kalman_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:20:09.203099+00:00
-- url     : https://prove2.me/theorems/0db178b7-2409-441d-8ea4-9d93667d5288
-- title:
--   Schur block observation update yields the exact scalar Kalman innovation posterior mean
-- statement:
--   Consider a block Gaussian observation linear system, with inverse action A on its leading block, cross-covariance row functional l, previous observation vector u, cross-vector b, solution variables x and w, and last observation v. If the last diagonal equals q+r+l(A b), with positive predicted state variance q and observation noise r, then the new posterior mean l(Au)+q w equals the Kalman innovation update l(Au)+[q/(q+r)](v-l(Au)). This directly transforms the abstract Schur scalar-elimination identity into the sequential Kalman mean update, with no specific matrix dimensions beyond a finite leading block.
-- source:
--   Särkkä and Solin (2019), Applied Stochastic Differential Equations, chapters 10 and 12: Gaussian conditional mean via Schur complement.

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_schur_block_scalar_elimination

theorem AppliedSDE.SarkkaSolin.schur_linear_system_to_kalman_mean
    (n : ℕ)
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (l : (Fin n → ℝ) →ₗ[ℝ] ℝ)
    (u b x : Fin n → ℝ) (w q r v : ℝ)
    (hq : 0 < q) (hr : 0 < r)
    (hx : x = A (u - w • b))
    (hrow : l x + (q + r + l (A b)) * w = v) :
    l (A u) + q * w =
      l (A u) + q / (q + r) * (v - l (A u)) := by
  sorry
