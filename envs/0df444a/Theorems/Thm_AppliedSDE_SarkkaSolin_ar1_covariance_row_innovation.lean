-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_covariance_row_innovation
-- name    : AppliedSDE.SarkkaSolin.ar1_covariance_row_innovation
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T00:20:28.072195+00:00
-- url     : https://prove2.me/theorems/6f5c6db1-0b68-4fbe-9cc5-14d298c44a56
-- title:
--   AR(1) covariance appended-row innovation is supported only at the new state
-- statement:
--   For the stationary scalar AR(1) covariance K_ij=V a^|i−j|, subtracting a times row n from row n+1 gives zero at all earlier observation coordinates i<=n and gives V(1−a²) at the newly appended diagonal i=n+1. This exact sparse innovation identity captures the Markov structure needed for Schur-complement induction in the open general Gaussian-process versus sequential Kalman theorem.
-- source:
--   Särkkä and Solin, Applied Stochastic Differential Equations (2019), Chapters 10 and 12, AR(1) Gaussian state-space kernel.

import Mathlib

theorem AppliedSDE.SarkkaSolin.ar1_covariance_row_innovation
    (n : ℕ) (a V : ℝ) (i : Fin (n + 2)) :
    V * a ^ Nat.dist (n + 1) i.val -
      a * (V * a ^ Nat.dist n i.val) =
    if i.val = n + 1 then V * (1 - a ^ 2) else 0 := by
  sorry
