-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_last_covariance_propagates
-- name    : AppliedSDE.SarkkaSolin.ar1_last_covariance_propagates
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T00:13:17.763498+00:00
-- url     : https://prove2.me/theorems/9f108d75-b953-4e64-865c-081b50036712
-- title:
--   Stationary AR(1) appended-state covariance propagates by the transition factor
-- statement:
--   For the stationary AR(1) covariance kernel K_ij=V a^|i-j|, the covariance between the newly appended state n+1 and any existing state i<=n equals a times the covariance between n and i. This exact finite-grid algebra is used in the Schur-complement/conditional Gaussian induction connecting batch GP regression to sequential Kalman filtering. The theorem imposes no positivity assumptions, as it follows simply from natural-number distances and powers.
-- source:
--   Särkkä and Solin, Applied Stochastic Differential Equations (2019), Chapters 10 and 12, stationary OU/AR1 covariance.

import Mathlib

theorem AppliedSDE.SarkkaSolin.ar1_last_covariance_propagates
    (n : ℕ) (a V : ℝ) (i : Fin (n + 1)) :
    V * a ^ Nat.dist (n + 1) i.val =
      a * (V * a ^ Nat.dist n i.val) := by
  sorry
