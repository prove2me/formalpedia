-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_noisy_covariance_append_block
-- name    : AppliedSDE.SarkkaSolin.ar1_noisy_covariance_append_block
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:06:37.125879+00:00
-- url     : https://prove2.me/theorems/a4e1a508-e966-4655-93cf-6cf26f2d2873
-- title:
--   Noisy AR(1) observation covariance block decomposition under an appended observation
-- statement:
--   For the stationary AR(1) observation covariance matrix C=K+rI with K(i,j)=Va^|i-j|, enlarging the sample from n+1 to n+2 observations preserves C as the top-left principal block, introduces appended cross-covariances k_i=Va^(n+1-i), and has lower-right diagonal V+r. This identifies the full 2-by-2 block partition needed to apply the Gaussian Schur complement inverse and prove that the old GP batch update agrees with the sequential Kalman filter after a new observation.
-- source:
--   Särkkä and Solin, Applied Stochastic Differential Equations (2019), Chapters 10 and 12; stationary OU covariance plus independent observation noise.

import Mathlib
open Matrix

theorem AppliedSDE.SarkkaSolin.ar1_noisy_covariance_append_block
    (n : ℕ) (a V r : ℝ) :
    let Cnew : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
      (Matrix.of (fun i j => V * a ^ Nat.dist i.val j.val)) +
        r • (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ)
    let Cold : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
      (Matrix.of (fun i j => V * a ^ Nat.dist i.val j.val)) +
        r • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    Cnew.submatrix Fin.castSucc Fin.castSucc = Cold ∧
      (∀ i : Fin (n + 1),
        Cnew (Fin.castSucc i) (Fin.last (n + 1)) =
          V * a ^ (n + 1 - i.val)) ∧
      Cnew (Fin.last (n + 1)) (Fin.last (n + 1)) = V + r := by
  sorry
