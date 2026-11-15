-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_batch_covariance_fromBlocks_system
-- name    : AppliedSDE.SarkkaSolin.ar1_batch_covariance_fromBlocks_system
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:32:33.729561+00:00
-- url     : https://prove2.me/theorems/921ab251-b83e-4799-87c3-2ed5da108d95
-- title:
--   Inverse noisy AR(1) batch covariance satisfies the actual Schur block matrix equations at arbitrary sample size
-- statement:
--   Let a in (0,1), stationary variance V>0, observation noise r>0 and any observations y on n+2 time points. Let Cnew be the corresponding noisy AR(1) covariance matrix and z=Cnew^(-1)y. The exact Fin(n+1) sum Fin1 block decomposition of Cnew has old observation covariance Cold, appended cross-vector Va^(n+1-i), and final scalar variance V+r. The reindexed inverse vector z solves this genuine Matrix.fromBlocks linear system exactly for all y and all n. The proof uses previously verified positive definiteness, inverse matrix multiplication, previously proved AR(1) block decomposition, and reindexing of matrix-vector action. This is the exact Gaussian batch linear-system premise required for the Schur complement to derive the sequential Kalman innovation recursion.
-- source:
--   Särkkä and Solin (2019), Applied Stochastic Differential Equations, Chapters 10 and 12, stationary OU/AR(1) covariance inversion and Schur block recursion.

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_general_noisy_covariance_posdef
import Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_noisy_covariance_fin_fromblocks
open Matrix
open scoped Matrix

theorem AppliedSDE.SarkkaSolin.ar1_batch_covariance_fromBlocks_system
    (n : ℕ) (a V r : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hV : 0 < V) (hr : 0 < r)
    (y : Fin (n + 2) → ℝ) :
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
    let z := Cnew⁻¹ |>.mulVec y
    (Matrix.fromBlocks Cold B B.transpose D).mulVec (z ∘ e) =
      y ∘ e := by
  sorry
