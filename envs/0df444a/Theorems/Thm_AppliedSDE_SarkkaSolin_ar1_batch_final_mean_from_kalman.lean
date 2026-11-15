-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_batch_final_mean_from_kalman
-- name    : AppliedSDE.SarkkaSolin.ar1_batch_final_mean_from_kalman
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T11:20:39.218662+00:00
-- url     : https://prove2.me/theorems/6b95cbd3-0476-4034-972f-3ea8bac606c4
-- title:
--   AR1 batch posterior mean agrees with recursive Kalman mean
-- statement:
--   For stationary AR1 covariance with positive observation noise, the final batch GP posterior mean equals the scalar Kalman filtered mean defined by its recursion, given initial variance and mean, positive dynamics, and recursion assumptions.
-- source:
--   Sarkka and Solin (2019), stationary OU/AR1 Gaussian process Kalman induction; decomposed from published joint theorem c3f40840-6868-47d7-9a32-72df6d60b5ea.

import Mathlib
open Matrix
open scoped Matrix

theorem AppliedSDE.SarkkaSolin.ar1_batch_final_mean_from_kalman
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
      (K.mulVec (C⁻¹ |>.mulVec y)) (Fin.last n)) := by
  sorry
