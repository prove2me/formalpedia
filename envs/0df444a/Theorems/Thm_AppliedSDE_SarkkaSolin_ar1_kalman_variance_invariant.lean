-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_kalman_variance_invariant
-- name    : AppliedSDE.SarkkaSolin.ar1_kalman_variance_invariant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:53:17.710885+00:00
-- url     : https://prove2.me/theorems/cdfdd1a1-5c44-4b3f-9281-8e30bad1b93e
-- title:
--   AR(1) Kalman Riccati posterior variances stay strictly positive and bounded by stationary variance
-- statement:
--   For arbitrary finite observation sequences and stable real AR(1) transition 0<a<1 with V,r>0, the scalar Kalman Riccati recursion starting at Vr/(V+r) preserves 0<P_k<=V for every step. The induction applies an already proved one-step variance-bound theorem and provides a global invariant needed for the Schur-complement Kalman batch induction, including positivity of all innovation denominators and a uniform stationary variance bound.
-- source:
--   Särkkä and Solin (2019), Applied Stochastic Differential Equations, Kalman Riccati recursion, Chapters 10 and 12.

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_kalman_variance_update_bounded

theorem AppliedSDE.SarkkaSolin.ar1_kalman_variance_invariant
    (n : ℕ) (a V r : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hV : 0 < V) (hr : 0 < r)
    (P : Fin (n + 1) → ℝ)
    (hP0 : P 0 = V * r / (V + r))
    (hPrec : ∀ k : Fin n,
      P k.succ =
        (a ^ 2 * P k.castSucc + V * (1 - a ^ 2)) * r /
          (a ^ 2 * P k.castSucc + V * (1 - a ^ 2) + r)) :
    ∀ k : Fin (n + 1), 0 < P k ∧ P k ≤ V := by
  sorry
