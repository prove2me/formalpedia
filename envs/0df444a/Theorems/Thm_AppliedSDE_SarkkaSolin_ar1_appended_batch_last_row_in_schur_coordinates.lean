-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_appended_batch_last_row_in_schur_coordinates
-- name    : AppliedSDE.SarkkaSolin.ar1_appended_batch_last_row_in_schur_coordinates
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T16:52:23.191508+00:00
-- url     : https://prove2.me/theorems/0057aa66-f393-46b4-88c6-4b4937ebe3dd
-- title:
--   AR1 batch posterior final coordinate in the exact Schur-block row representation
-- statement:
--   The final coordinate of the AR1 covariance matrix-vector product is the new-state Schur block row: a times the previous last covariance row dotted with the old-coordinate vector, plus V times the appended coordinate. The finSumFinEquiv indexing matches actual batch data. Supports direct instantiation of the Proved generic Schur/Kalman update on the true indexed covariance matrix.
-- source:
--   Sarkka and Solin (2019), OU-GP batch Kalman recursion; uses previously established appended last covariance row and cross-covariance scaling.

import Mathlib
open Matrix
open scoped Matrix

theorem AppliedSDE.SarkkaSolin.ar1_appended_batch_last_row_in_schur_coordinates
    (n : ℕ) (a V : ℝ) (z : Fin (n + 2) -> ℝ) :
    let e : (Fin (n + 1) ⊕ Fin 1) ≃ Fin (n + 2) := finSumFinEquiv
    let K : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
      Matrix.of fun i j => V * a ^ Nat.dist i.val j.val
    let kold : Fin (n + 1) -> ℝ :=
      fun i => V * a ^ Nat.dist n i.val
    (K.mulVec z) (Fin.last (n + 1)) =
      ((a • kold) ⬝ᵥ ((z ∘ e) ∘ Sum.inl)) +
        V * (z ∘ e) (Sum.inr (0 : Fin 1)) := by
  sorry
