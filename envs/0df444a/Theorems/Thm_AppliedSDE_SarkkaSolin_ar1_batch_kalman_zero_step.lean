-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_batch_kalman_zero_step
-- name    : AppliedSDE.SarkkaSolin.ar1_batch_kalman_zero_step
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:55:28.713788+00:00
-- url     : https://prove2.me/theorems/870aec9d-6e92-4f3d-8076-34abddf1a3ae
-- title:
--   Single-observation stationary AR(1) GP posterior equals initial Kalman update
-- statement:
--   For a one-dimensional stationary Gaussian state X_0 with variance V>0 and a single noisy observation Y_0 with independent variance r>0, the batch GP posterior mean K(K+rI)^{-1}Y_0 equals V/(V+r)Y_0. This is the n=0 base case of the general AR1 batch-versus-sequential Kalman theorem 1b230031-7f34-4971-8d05-2f91cf171bd9, and uses the exact inverse identity for the positive 1×1 observation matrix.
-- source:
--   Särkkä and Solin, Applied Stochastic Differential Equations (2019), Chapters 10 and 12.

import Mathlib
open Matrix

theorem AppliedSDE.SarkkaSolin.ar1_batch_kalman_zero_step
    (V r : ℝ) (hV : 0 < V) (hr : 0 < r)
    (y : Fin 1 → ℝ) :
    let K : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => V
    (K.mulVec (((K + r • (1 : Matrix (Fin 1) (Fin 1) ℝ))⁻¹).mulVec y)) 0 =
      V / (V + r) * y 0 := by
  sorry
