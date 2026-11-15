-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_next_cross_covariance_mulvec
-- name    : AppliedSDE.SarkkaSolin.ar1_next_cross_covariance_mulvec
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:48:58.722419+00:00
-- url     : https://prove2.me/theorems/50ed8bba-e20f-4921-863c-323b7563ca85
-- title:
--   AR(1) next-state cross-covariance applied to a vector equals predicted last-state covariance
-- statement:
--   For stationary AR(1) covariance kernel K(i,j)=V a^|i-j| and any weight vector z over observations through time n, the cross-covariance of the next state with those observations, summed against z, equals a times the same weights applied to the current last-state covariance row. This is the exact covariance prediction identity k^T z = a (Kz)_n that forms the GP batch to Kalman Schur-complement induction step.
-- source:
--   Särkkä and Solin, Applied Stochastic Differential Equations (2019), Chapters 10 and 12: OU covariance and Kalman prediction.

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_last_covariance_propagates
open scoped BigOperators

theorem AppliedSDE.SarkkaSolin.ar1_next_cross_covariance_mulvec
    (n : ℕ) (a V : ℝ) (z : Fin (n + 1) → ℝ) :
    (∑ j : Fin (n + 1),
      (V * a ^ Nat.dist (n + 1) j.val) * z j) =
    a * (∑ j : Fin (n + 1),
      (V * a ^ Nat.dist n j.val) * z j) := by
  sorry
