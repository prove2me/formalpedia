-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_true_covariance_append_joint_kalman_step
-- name    : AppliedSDE.SarkkaSolin.ar1_true_covariance_append_joint_kalman_step
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T16:54:03.990117+00:00
-- url     : https://prove2.me/theorems/60dd39e3-48b7-423a-8199-2178e1b0f177
-- title:
--   True indexed AR1 batch covariance joint Schur/Kalman mean and variance one-step update
-- statement:
--   For the true indexed finite AR1 noisy covariance matrices and the actual final-state covariance column, if the old inverse matrix and old batch mean/variance equal the supplied values and the appended Schur denominator is nonzero, then the enlarged batch posterior mean and variance obey the exact scalar Kalman update with predicted variance a^2*Pold+V*(1-a^2). This connects the generic Schur joint update to the original batch finite-index representation.
-- source:
--   Sarkka and Solin (2019), OU Gaussian-process regression versus AR1 Kalman recursion; sourced in Prove2Me proven generic Schur block joint update, true covariance fromBlocks equations and last-row bridge.

import Mathlib
open Matrix
open scoped Matrix

theorem AppliedSDE.SarkkaSolin.ar1_true_covariance_append_joint_kalman_step
    (n : ℕ) (a V r : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hV : 0 < V) (hr : 0 < r)
    (y : Fin (n + 2) -> ℝ) (Pold mold : ℝ) :
    let Cold : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
      (Matrix.of fun i j => V * a ^ Nat.dist i.val j.val) +
        r • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    let Cnew : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
      (Matrix.of fun i j => V * a ^ Nat.dist i.val j.val) +
        r • (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ)
    let Knew : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
      Matrix.of fun i j => V * a ^ Nat.dist i.val j.val
    let e : (Fin (n + 1) ⊕ Fin 1) ≃ Fin (n + 2) := finSumFinEquiv
    let kold : Fin (n + 1) -> ℝ :=
      fun i => V * a ^ Nat.dist n i.val
    let knew : Fin (n + 2) -> ℝ :=
      fun i => V * a ^ Nat.dist (n + 1) i.val
    let zM := Cnew⁻¹ |>.mulVec y
    let zV := Cnew⁻¹ |>.mulVec knew
    let pred : ℝ := a ^ 2 * Pold + V * (1 - a ^ 2)
    Cold⁻¹ * Cold = 1 ->
    Pold = V - (kold ⬝ᵥ (Cold⁻¹).mulVec kold) ->
    mold = kold ⬝ᵥ (Cold⁻¹).mulVec (fun i : Fin (n + 1) => y i.castSucc) ->
    (V + r) - ((a • kold) ⬝ᵥ (Cold⁻¹).mulVec (a • kold)) ≠ 0 ->
    ((Knew.mulVec zM) (Fin.last (n + 1)) =
      a * mold + pred / (pred + r) *
        (y (Fin.last (n + 1)) - a * mold)) ∧
    (V - (Knew.mulVec zV) (Fin.last (n + 1)) =
      pred * r / (pred + r)) := by
  sorry
