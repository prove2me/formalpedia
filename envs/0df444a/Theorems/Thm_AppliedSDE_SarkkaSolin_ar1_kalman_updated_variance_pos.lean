-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_kalman_updated_variance_pos
-- name    : AppliedSDE.SarkkaSolin.ar1_kalman_updated_variance_pos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:48:12.856584+00:00
-- url     : https://prove2.me/theorems/a365cc66-d6a4-48cf-b4af-8735cd978284
-- title:
--   Positive Kalman filtering posterior variances at every AR(1) observation step
-- statement:
--   For a stable real AR(1) coefficient 0<a<1, positive stationary variance V and observation noise r, any finite sequence of Kalman posterior variances P with initial P0=Vr/(V+r) and scalar Riccati update P_(k+1)=[a² P_k+V(1-a²)]r/[a²P_k+V(1-a²)+r] remains strictly positive for every index. This supplies positive predicted variance and nonzero denominators throughout the arbitrary-sample-size Gaussian-process/Kalman equivalence induction.
-- source:
--   Särkkä and Solin, Applied Stochastic Differential Equations (2019), Chapters 10 and 12 (scalar Kalman Riccati recursion).

import Mathlib

theorem AppliedSDE.SarkkaSolin.ar1_kalman_updated_variance_pos
    (n : ℕ) (a V r : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hV : 0 < V) (hr : 0 < r)
    (P : Fin (n + 1) → ℝ)
    (hP0 : P 0 = V * r / (V + r))
    (hPrec : ∀ k : Fin n,
      P k.succ =
        (a ^ 2 * P k.castSucc + V * (1 - a ^ 2)) * r /
          (a ^ 2 * P k.castSucc + V * (1 - a ^ 2) + r)) :
    ∀ k : Fin (n + 1), 0 < P k := by
  sorry
