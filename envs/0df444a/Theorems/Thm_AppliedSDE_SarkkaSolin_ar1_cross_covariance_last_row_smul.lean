-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_cross_covariance_last_row_smul
-- name    : AppliedSDE.SarkkaSolin.ar1_cross_covariance_last_row_smul
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T16:47:16.513962+00:00
-- url     : https://prove2.me/theorems/3e32dcf5-3a62-4ed6-a47a-60bb469076a6
-- title:
--   AR1 new cross-covariance row equals autoregressive coefficient times previous last row
-- statement:
--   For AR1 covariance K(i,j)=V*a^|i-j|, the cross covariance of the newly appended time n+1 with every old observation is exactly a times the previous time n covariance row. This bridges the indexed stationary GP covariance block with the Schur Kalman update.
-- source:
--   Sarkka and Solin (2019), OU and AR1 Gaussian-process/Kalman equivalence; elementary finite-index exponent identity.

import Mathlib
open Matrix
open scoped Matrix

theorem AppliedSDE.SarkkaSolin.ar1_cross_covariance_last_row_smul
    (n : ℕ) (a V : ℝ) :
    (fun i : Fin (n + 1) => V * a ^ (n + 1 - i.val)) =
      a • (fun i : Fin (n + 1) => V * a ^ Nat.dist n i.val) := by
  sorry
