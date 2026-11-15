-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_gp_batch_final_innovation_equation
-- name    : AppliedSDE.SarkkaSolin.ar1_gp_batch_final_innovation_equation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:12:09.033315+00:00
-- url     : https://prove2.me/theorems/a2b22acb-e2f7-43de-abd9-7c5726d60af8
-- title:
--   Universal finite-sample AR(1) GP batch posterior satisfies innovation equation
-- statement:
--   For every positive sample size and every stable positive AR(1) transition a in (0,1), stationary variance V>0, noise variance r>0 and observation vector y, define K_ij=Va^|i-j| and batch posterior mean m=K(K+rI)^(-1)y. Then (r+V(1-a²)) m_last = ar m_penultimate + V(1-a²) y_last, with no separate invertibility or positive-definiteness assumption. The proof combines general AR(1) noisy covariance positive definiteness with the matrix-vector batch posterior innovation theorem, providing an explicit universal linear equation for the Kalman equivalence capstone.
-- source:
--   Särkkä and Solin (2019), Applied Stochastic Differential Equations, Chapters 10 and 12.

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_general_noisy_covariance_posdef
import Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_batch_posterior_innovation
open Matrix

theorem AppliedSDE.SarkkaSolin.ar1_gp_batch_final_innovation_equation
    (n : ℕ) (a V r : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hV : 0 < V) (hr : 0 < r)
    (y : Fin (n + 2) → ℝ) :
    let K : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
      Matrix.of fun i j => V * a ^ Nat.dist i.val j.val
    let z := (K + r • (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ))⁻¹ |>.mulVec y
    let m := K.mulVec z
    (r + V * (1 - a ^ 2)) * m (Fin.last (n + 1)) =
      a * r * m ((Fin.last n).castSucc) +
        V * (1 - a ^ 2) * y (Fin.last (n + 1)) := by
  sorry
