-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_gp_batch_next_state_predicted_mean
-- name    : AppliedSDE.SarkkaSolin.ar1_gp_batch_next_state_predicted_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:02:57.048993+00:00
-- url     : https://prove2.me/theorems/14249d0b-aa7b-4182-8790-0f9b4e87130c
-- title:
--   AR(1) next-state GP cross-covariance regression prediction is a times the previous posterior mean
-- statement:
--   Let K be the stationary AR(1) covariance matrix on observations 0 to n, z=(K+rI)^(-1)y and the GP batch posterior mean m=Kz. For the next state, the cross-covariance vector has entries Va^|n+1-j|. Its regression prediction against the old observations, k_next dot z, equals a times the last coordinate of m. This is the precise Gaussian-process predicted-mean identity needed for an inductive proof that the OU/AR(1) GP batch posterior equals the sequential Kalman filter.
-- source:
--   Särkkä and Solin (2019), Applied Stochastic Differential Equations, Chapters 10 and 12: prediction of GP conditional mean for AR(1).

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_next_cross_covariance_mulvec
open Matrix
open scoped BigOperators Matrix

theorem AppliedSDE.SarkkaSolin.ar1_gp_batch_next_state_predicted_mean
    (n : ℕ) (a V r : ℝ)
    (y : Fin (n + 1) → ℝ) :
    let K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
      fun i j => V * a ^ Nat.dist i.val j.val
    let z := (K + r • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ))⁻¹ |>.mulVec y
    (∑ j : Fin (n + 1),
      (V * a ^ Nat.dist (n + 1) j.val) * z j) =
      a * (K.mulVec z) (Fin.last n) := by
  sorry
