-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_kalman_schur_innovation_positive_from_recursion
-- name    : AppliedSDE.SarkkaSolin.ar1_kalman_schur_innovation_positive_from_recursion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T16:51:43.615109+00:00
-- url     : https://prove2.me/theorems/363a318e-3de1-42bd-b890-bb0c85909c1e
-- title:
--   Positive AR1 batch Kalman Schur innovation denominator from finite Riccati recursion
-- statement:
--   If a finite scalar Kalman variance recursion has the stationary initial condition and coincides at its last index with the batch covariance posterior variance, then the appended-observation Schur innovation denominator is positive. Uses the finite recursion nonnegativity and the proved scalar AR1 innovation denominator identity.
-- source:
--   Sarkka and Solin (2019), AR1 batch versus sequential Kalman covariance induction.

import Mathlib
open Matrix
open scoped Matrix

theorem AppliedSDE.SarkkaSolin.ar1_kalman_schur_innovation_positive_from_recursion
    (n : ℕ) (a V r : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hV : 0 < V) (hr : 0 < r)
    (P : Fin (n + 1) -> ℝ)
    (hP0 : P 0 = V * r / (V + r))
    (hstep : ∀ j : Fin n,
      P j.succ =
        (a ^ 2 * P j.castSucc + V * (1 - a ^ 2)) * r /
          (a ^ 2 * P j.castSucc + V * (1 - a ^ 2) + r))
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (k : Fin (n + 1) -> ℝ)
    (hPident : P (Fin.last n) = V - (k ⬝ᵥ A.mulVec k)) :
    0 < (V + r) - ((a • k) ⬝ᵥ A.mulVec (a • k)) := by
  sorry
