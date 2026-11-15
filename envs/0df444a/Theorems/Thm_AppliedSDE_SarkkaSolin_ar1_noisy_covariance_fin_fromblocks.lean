-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_noisy_covariance_fin_fromblocks
-- name    : AppliedSDE.SarkkaSolin.ar1_noisy_covariance_fin_fromblocks
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:06:36.026466+00:00
-- url     : https://prove2.me/theorems/d3278764-b819-4f39-9ebe-16702e5c4fe4
-- title:
--   Reindexing the noisy AR(1) covariance extension as a genuine 2x2 matrix.fromBlocks
-- statement:
--   Let C_(n+2) be the noisy AR(1) stationary covariance matrix with entries Va^|i-j|+r*delta_ij, and C_(n+1) the previous observation covariance. Under the canonical equivalence Fin(n+1) sum Fin1 to Fin(n+2), the enlarged matrix is exactly Matrix.fromBlocks(C_(n+1), B, B^T, [V+r]), with B_i=Va^(n+1-i). This establishes the complete matrix-level block decomposition, including the index equivalence, required to apply Mathlib SchurComplement inverse theorems and prove Gaussian-process batch posterior equals sequential Kalman filtering for arbitrary sample sizes.
-- source:
--   Särkkä and Solin (2019), Applied Stochastic Differential Equations, Chapters 10 and 12; Mathlib Matrix.fromBlocks and finSumFinEquiv.

import Mathlib
open Matrix
open scoped Matrix

theorem AppliedSDE.SarkkaSolin.ar1_noisy_covariance_fin_fromblocks
    (n : ℕ) (a V r : ℝ) :
    let e : (Fin (n + 1) ⊕ Fin 1) ≃ Fin (n + 2) := finSumFinEquiv
    let Cnew : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
      (Matrix.of (fun i j => V * a ^ Nat.dist i.val j.val)) +
        r • (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ)
    let Cold : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
      (Matrix.of (fun i j => V * a ^ Nat.dist i.val j.val)) +
        r • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    let B : Matrix (Fin (n + 1)) (Fin 1) ℝ :=
      fun i _ => V * a ^ (n + 1 - i.val)
    let D : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => V + r
    Cnew.submatrix e e = Matrix.fromBlocks Cold B B.transpose D := by
  sorry
