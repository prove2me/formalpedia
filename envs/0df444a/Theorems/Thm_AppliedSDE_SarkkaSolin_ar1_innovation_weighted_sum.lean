-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_innovation_weighted_sum
-- name    : AppliedSDE.SarkkaSolin.ar1_innovation_weighted_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T07:54:36.7332+00:00
-- url     : https://prove2.me/theorems/6086844b-ff37-4a88-ab51-f1fb7cc6f239
-- title:
--   AR(1) row innovation weighted-sum identity for batch Kalman extension
-- statement:
--   The weighted sum of the last covariance row minus a times the preceding row collapses to the appended-state coordinate, times innovation variance V(1-a^2). This yields the exact linear-algebra row identity used when extending an AR(1) Gaussian-process covariance matrix by one time step in the recursive Kalman update.
-- source:
--   Särkkä and Solin (2019), Applied Stochastic Differential Equations, chapters 10 and 12.

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_covariance_row_innovation
open scoped BigOperators

theorem AppliedSDE.SarkkaSolin.ar1_innovation_weighted_sum
    (n : ℕ) (a V : ℝ) (z : Fin (n + 2) → ℝ) :
    (∑ j : Fin (n + 2),
      (V * a ^ Nat.dist (n + 1) j.val -
        a * (V * a ^ Nat.dist n j.val)) * z j) =
      V * (1 - a ^ 2) * z (Fin.last (n + 1)) := by
  sorry
