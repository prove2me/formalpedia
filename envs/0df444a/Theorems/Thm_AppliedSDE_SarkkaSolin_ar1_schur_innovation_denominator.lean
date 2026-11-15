-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_schur_innovation_denominator
-- name    : AppliedSDE.SarkkaSolin.ar1_schur_innovation_denominator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:32:49.941476+00:00
-- url     : https://prove2.me/theorems/3b218d76-ec3b-4954-a679-a9b77df2baa4
-- title:
--   AR(1) Schur-complement denominator equals the Kalman innovation variance and is strictly positive
-- statement:
--   For any stationary scalar AR(1) transition 0<a<1, V>0, r>0, a covariance inverse matrix A and previous cross-vector k whose conditional posterior variance is P=V-k^T A k>=0, the scalar Schur complement of the appended noisy observation is S=(V+r)-(a k)^T A (a k)=a²P+V(1-a²)+r, and S>0. This proves both the exact identity and nonzero denominator needed when applying the Schur block inverse to the new observation; it matches the Kalman innovation covariance at arbitrary batch size.
-- source:
--   Särkkä and Solin (2019), Applied Stochastic Differential Equations, Chapters 10 and 12, noisy AR(1) Gaussian Schur complement and Kalman innovations.

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_schur_predicted_variance
open Matrix
open scoped Matrix

theorem AppliedSDE.SarkkaSolin.ar1_schur_innovation_denominator
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (k : Fin n → ℝ) (a V r P : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hV : 0 < V)
    (hr : 0 < r) (hP : 0 ≤ P)
    (hPident : P = V - (k ⬝ᵥ A.mulVec k)) :
    ((V + r) - ((a • k) ⬝ᵥ A.mulVec (a • k)) =
      (a ^ 2 * P + V * (1 - a ^ 2)) + r) ∧
    0 < (V + r) - ((a • k) ⬝ᵥ A.mulVec (a • k)) := by
  sorry
