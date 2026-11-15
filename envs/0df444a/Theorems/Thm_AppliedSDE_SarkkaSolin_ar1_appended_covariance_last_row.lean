-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_appended_covariance_last_row
-- name    : AppliedSDE.SarkkaSolin.ar1_appended_covariance_last_row
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T16:46:11.406242+00:00
-- url     : https://prove2.me/theorems/e5b8223b-9985-464d-9bc6-cd62b149b718
-- title:
--   AR1 appended covariance last-row matrix-vector decomposition
-- statement:
--   The final row of the enlarged AR1 covariance matrix applied to a vector equals its old-block cross-covariance row dot the prefix vector plus V times the new last vector entry. The old-block weights are V*a^(n+1-i). This is an indexed bridge for the Schur-complement batch Kalman induction.
-- source:
--   Sarkka and Solin (2019), AR1/OU covariance and Kalman filter; from the finite matrix last-row split and Nat.dist_eq_sub_of_le_right.

import Mathlib
open Matrix
open scoped Matrix

theorem AppliedSDE.SarkkaSolin.ar1_appended_covariance_last_row
    (n : ℕ) (a V : ℝ) (z : Fin (n + 2) -> ℝ) :
    let K : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
      Matrix.of fun i j => V * a ^ Nat.dist i.val j.val
    (K.mulVec z) (Fin.last (n + 1)) =
      (fun i : Fin (n + 1) => V * a ^ (n + 1 - i.val))
        ⬝ᵥ (fun i => z i.castSucc) +
      V * z (Fin.last (n + 1)) := by
  sorry
