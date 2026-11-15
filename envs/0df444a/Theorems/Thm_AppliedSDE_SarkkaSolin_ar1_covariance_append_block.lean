-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_covariance_append_block
-- name    : AppliedSDE.SarkkaSolin.ar1_covariance_append_block
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:03:01.737215+00:00
-- url     : https://prove2.me/theorems/4f148f27-a67e-4966-bc32-c8aedaa4000b
-- title:
--   AR(1) enlarged stationary covariance decomposes into old principal block, appended cross-vector and variance
-- statement:
--   For stationary AR(1) covariance K(i,j)=Va^|i-j|, the enlarged (n+2)-state covariance matrix has old principal block exactly equal to the original (n+1)-state covariance under Fin.castSucc, its appended column cross-covariance is k_i=Va^(n+1-i), and its final diagonal entry is V. This fully identifies the three constituent blocks used in the finite-dimensional Schur complement induction proving batch Gaussian-process regression equals sequential Kalman filtering.
-- source:
--   Särkkä and Solin (2019), Applied Stochastic Differential Equations, Chapters 10 and 12, stationary scalar OU/AR(1) covariance block extension.

import Mathlib
open Matrix

theorem AppliedSDE.SarkkaSolin.ar1_covariance_append_block
    (n : ℕ) (a V : ℝ) :
    let Knew : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
      fun i j => V * a ^ Nat.dist i.val j.val
    let Kold : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
      fun i j => V * a ^ Nat.dist i.val j.val
    Knew.submatrix Fin.castSucc Fin.castSucc = Kold ∧
      (∀ i : Fin (n + 1),
        Knew (Fin.castSucc i) (Fin.last (n + 1)) =
          V * a ^ (n + 1 - i.val)) ∧
      Knew (Fin.last (n + 1)) (Fin.last (n + 1)) = V := by
  sorry
