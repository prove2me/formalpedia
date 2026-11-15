-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_batch_zero_step_variance_matrix
-- name    : AppliedSDE.SarkkaSolin.ar1_batch_zero_step_variance_matrix
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T16:42:59.386778+00:00
-- url     : https://prove2.me/theorems/700d4321-8cd1-4d83-ac21-67ce3668824f
-- title:
--   AR1 Kalman posterior variance base case as a one-coordinate matrix inverse
-- statement:
--   The posterior variance of one scalar Gaussian state with prior variance V and noisy observation variance r, computed from the one-coordinate covariance matrix, equals V*r/(V+r). This is the n=0 induction base for the batch Kalman variance identity.
-- source:
--   Sarkka and Solin (2019), Gaussian conditioning/Kalman filter; reuse Prove2Me theorem AppliedSDE.SarkkaSolin.ar1_batch_kalman_zero_step.

import Mathlib
open Matrix
open scoped Matrix

theorem AppliedSDE.SarkkaSolin.ar1_batch_zero_step_variance_matrix
    (V r : ℝ) (hV : 0 < V) (hr : 0 < r) :
    let K : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => V
    let k : Fin 1 -> ℝ := fun _ => V
    V - (k ⬝ᵥ (((K + r • (1 : Matrix (Fin 1) (Fin 1) ℝ))⁻¹).mulVec k)) =
      V * r / (V + r) := by
  sorry
