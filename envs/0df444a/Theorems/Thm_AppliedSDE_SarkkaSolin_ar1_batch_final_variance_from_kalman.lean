-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_batch_final_variance_from_kalman
-- name    : AppliedSDE.SarkkaSolin.ar1_batch_final_variance_from_kalman
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T11:20:39.539488+00:00
-- url     : https://prove2.me/theorems/0347b681-ceb6-40c5-bdf5-e6b0c3148b3c
-- title:
--   AR1 batch posterior variance agrees with recursive Kalman variance
-- statement:
--   For stationary AR1 covariance with positive observation noise, the final batch GP posterior variance equals the scalar Kalman filtered variance defined by its recursion. This supplies the Schur complement variance step of the joint Gaussian conditioning induction.
-- source:
--   Sarkka and Solin (2019), stationary OU/AR1 Gaussian process Kalman induction; decomposed from published joint theorem c3f40840-6868-47d7-9a32-72df6d60b5ea.

import Mathlib
open Matrix
open scoped Matrix

theorem AppliedSDE.SarkkaSolin.ar1_batch_final_variance_from_kalman
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
    (P (Fin.last n) = V - (k ⬝ᵥ (C⁻¹ |>.mulVec k))) := by
  sorry
