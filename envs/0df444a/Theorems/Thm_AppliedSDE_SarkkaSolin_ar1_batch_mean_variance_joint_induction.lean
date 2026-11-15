-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_batch_mean_variance_joint_induction
-- name    : AppliedSDE.SarkkaSolin.ar1_batch_mean_variance_joint_induction
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T10:11:39.398381+00:00
-- url     : https://prove2.me/theorems/c3f40840-6868-47d7-9a32-72df6d60b5ea
-- title:
--   Inductive GP batch posterior mean and variance jointly equal the sequential AR(1) Kalman recursions
-- statement:
--   For any stable AR(1) transition 0<a<1, positive stationary variance V, observation variance r, any number n+1 of noisy observations, and the scalar Kalman filtering mean m and posterior variance P sequences defined by initial values and usual Riccati/innovation recursions, the final filtered mean equals the last component of the full Gaussian-process batch posterior K(K+rI)^(-1)y AND the final filtered variance equals the Gaussian conditional variance V-k^T(K+rI)^(-1)k for k the final-state covariance row. This stronger joint mean-and-variance invariant is the mathematically necessary induction hypothesis for the all-sample-size GP/Kalman equivalence. Its proof should apply the proved AR(1) block covariance decomposition, reindexed inverse linear-system bridge, Schur denominator identity, predicted mean, and scalar Kalman update.
-- source:
--   Särkkä and Solin (2019), Applied Stochastic Differential Equations, Chapters 10 and 12; Schur-complement proof of equivalence between batch Gaussian-process regression and sequential Kalman filtering.

import Mathlib
open Matrix
open scoped Matrix

theorem AppliedSDE.SarkkaSolin.ar1_batch_mean_variance_joint_induction
    (n : ℕ) (a V r : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hV : 0 < V) (hr : 0 < r)
    (y m P : Fin (n + 1) → ℝ) :
    let K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
      Matrix.of fun i j => V * a ^ Nat.dist i.val j.val
    let C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
      K + r • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    let k : Fin (n + 1) → ℝ := fun j => K (Fin.last n) j
    (P 0 = V * r / (V + r)) →
    (m 0 = V / (V + r) * y 0) →
    (∀ j : Fin n,
      let predicted : ℝ := a ^ 2 * P j.castSucc + V * (1 - a ^ 2)
      P j.succ = predicted * r / (predicted + r) ∧
      m j.succ = a * m j.castSucc +
        predicted / (predicted + r) *
          (y j.succ - a * m j.castSucc)) →
    (m (Fin.last n) =
      (K.mulVec (C⁻¹ |>.mulVec y)) (Fin.last n)) ∧
    (P (Fin.last n) = V - (k ⬝ᵥ (C⁻¹ |>.mulVec k))) := by
  sorry
