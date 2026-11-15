-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_covariance_mulvec_innovation
-- name    : AppliedSDE.SarkkaSolin.ar1_covariance_mulvec_innovation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T07:57:04.867305+00:00
-- url     : https://prove2.me/theorems/26bd2680-1388-4f3f-a85e-e517dc7b0832
-- title:
--   Stationary AR(1) covariance matrix-vector last-step innovation identity
-- statement:
--   For the stationary AR(1) covariance matrix indexed by n+2 points, the last row of its matrix-vector product minus a times the penultimate row equals the final vector coordinate times the state innovation variance V(1-a²). This is a coordinate-free matrix operation version of the weighted-sum innovation lemma, directly supporting the batch GP to sequential Kalman induction.
-- source:
--   Särkkä and Solin, Applied Stochastic Differential Equations (2019), Chapters 10 and 12.

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_innovation_weighted_sum
open scoped BigOperators

theorem AppliedSDE.SarkkaSolin.ar1_covariance_mulvec_innovation
    (n : ℕ) (a V : ℝ) (z : Fin (n + 2) → ℝ) :
    let K : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
      fun i j => V * a ^ Nat.dist i.val j.val
    (K.mulVec z) (Fin.last (n + 1)) -
      a * (K.mulVec z) ((Fin.last n).castSucc) =
        V * (1 - a ^ 2) * z (Fin.last (n + 1)) := by
  sorry
