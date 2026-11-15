-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_batch_posterior_innovation
-- name    : AppliedSDE.SarkkaSolin.ar1_batch_posterior_innovation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:08:08.035868+00:00
-- url     : https://prove2.me/theorems/9edbc03d-03fb-419f-a609-4b939521fc0e
-- title:
--   Batch AR(1) GP posterior satisfies last-row innovation balance
-- statement:
--   For any stationary AR(1) covariance matrix K whose noisy observation matrix K+rI is positive definite, define the batch GP posterior mean m=K(K+rI)^(-1)y. Its last coordinate and penultimate coordinate obey the exact backward-smoothing innovation equation (r+V(1-a²)) m_last = a r m_previous + V(1-a²) y_last. This follows from the matrix-vector covariance innovation and the batch posterior residual identity and is a reusable exact matrix algebra step towards Kalman equivalence.
-- source:
--   Särkkä and Solin (2019), Applied Stochastic Differential Equations, Chapters 10 and 12.

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_covariance_mulvec_innovation
import Theorems.Thm_AppliedSDE_SarkkaSolin_gp_batch_posterior_residual
open Matrix

theorem AppliedSDE.SarkkaSolin.ar1_batch_posterior_innovation
    (n : ℕ) (a V r : ℝ) (y : Fin (n + 2) → ℝ)
    (hM :
      ((Matrix.of (fun i j : Fin (n + 2) => V * a ^ Nat.dist i.val j.val)) +
          r • (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ)).PosDef) :
    let K : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
      Matrix.of fun i j => V * a ^ Nat.dist i.val j.val
    let z := (K + r • (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ))⁻¹ |>.mulVec y
    let m := K.mulVec z
    (r + V * (1 - a ^ 2)) * m (Fin.last (n + 1)) =
      a * r * m ((Fin.last n).castSucc) +
        V * (1 - a ^ 2) * y (Fin.last (n + 1)) := by
  sorry
