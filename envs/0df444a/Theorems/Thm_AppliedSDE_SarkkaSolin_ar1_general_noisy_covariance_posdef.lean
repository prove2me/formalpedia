-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_general_noisy_covariance_posdef
-- name    : AppliedSDE.SarkkaSolin.ar1_general_noisy_covariance_posdef
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:08:09.955184+00:00
-- url     : https://prove2.me/theorems/5a9212c8-d5a4-4766-98b3-0077ff076b81
-- title:
--   Positive definiteness of arbitrary stable AR(1) GP observation covariance
-- statement:
--   For any real AR(1) transition factor 0<a<1, stationary variance V>0, observation noise variance r>0 and sample size n+1, the matrix K+rI with K_ij=V a^|i-j| is strictly positive definite and therefore invertible. Derive this by representing the factor a as exp(-rate) with rate=-log(a)>0 and applying the previously proved OU-grid observation covariance positivity theorem. This removes an OU-specific parameter restriction from the general Kalman batch identity.
-- source:
--   Sarkka and Solin, Applied Stochastic Differential Equations (2019), chapters 10 and 12.

import Mathlib
import Definitions.Def_AppliedSDE_SarkkaSolin_OUKalmanInterfaces
import Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_noisy_covariance_posdef
open Matrix

theorem AppliedSDE.SarkkaSolin.ar1_general_noisy_covariance_posdef
    (n : ℕ) (a V r : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hV : 0 < V) (hr : 0 < r) :
    ((Matrix.of (fun i j : Fin (n + 1) => V * a ^ Nat.dist i.val j.val)) +
        r • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)).PosDef := by
  sorry
