-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_kalman_finite_recursion_variance_nonnegative
-- name    : AppliedSDE.SarkkaSolin.ar1_kalman_finite_recursion_variance_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T16:49:57.076863+00:00
-- url     : https://prove2.me/theorems/288dab24-84d4-453b-9eb7-cc6c18c7e25e
-- title:
--   Nonnegative filtered AR1 scalar Kalman variance at every finite recursion step
-- statement:
--   Given a stationary variance V>0, observation noise r>0 and AR1 coefficient a between zero and one, the scalar Kalman posterior variance sequence initialised at V*r/(V+r) and updated by its Riccati formula is nonnegative at every finite step. Supports positivity of the Schur innovation denominator in the finite AR1 batch-versus-sequential induction.
-- source:
--   Sarkka and Solin (2019), scalar Kalman filter Riccati recursion; induction on Fin (n+1).

import Mathlib

theorem AppliedSDE.SarkkaSolin.ar1_kalman_finite_recursion_variance_nonnegative
    (n : ℕ) (a V r : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hV : 0 < V) (hr : 0 < r)
    (P : Fin (n + 1) -> ℝ)
    (hP0 : P 0 = V * r / (V + r))
    (hstep : ∀ j : Fin n,
      P j.succ =
        (a ^ 2 * P j.castSucc + V * (1 - a ^ 2)) * r /
          (a ^ 2 * P j.castSucc + V * (1 - a ^ 2) + r)) :
    ∀ j : Fin (n + 1), 0 ≤ P j := by
  sorry
