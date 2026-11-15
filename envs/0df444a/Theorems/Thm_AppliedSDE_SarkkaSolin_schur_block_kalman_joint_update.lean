-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_schur_block_kalman_joint_update
-- name    : AppliedSDE.SarkkaSolin.schur_block_kalman_joint_update
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T13:45:59.804166+00:00
-- url     : https://prove2.me/theorems/24fb7707-b21b-4368-9041-15c7f5c1c980
-- title:
--   Kalman mean and Riccati variance recursions from symmetric Schur block systems
-- statement:
--   Assume a leading covariance block M has a left inverse A, a previous Gaussian-process mean and posterior variance satisfy the batch covariance identities, and two appended block covariance systems are solved for the observation vector and the covariance last column. The exact Schur complement identities yield simultaneously the scalar Kalman mean innovation update and variance Riccati update with predicted variance a squared times the prior posterior variance plus V times one minus a squared. This packages the common algebraic induction step independently of finite index reindexing.
-- source:
--   Sarkka and Solin (2019), Applied Stochastic Differential Equations, Gaussian-process equivalence with Kalman filtering, Chapters 10 and 12.

import Mathlib
open Matrix
open scoped Matrix

theorem AppliedSDE.SarkkaSolin.schur_block_kalman_joint_update
    (n : ℕ) (M A : Matrix (Fin n) (Fin n) ℝ)
    (hAM : A * M = 1)
    (k u : Fin n -> ℝ)
    (a V r Pold mold ynew : ℝ)
    (hP : Pold = V - (k ⬝ᵥ A.mulVec k))
    (hm : mold = k ⬝ᵥ A.mulVec u)
    (zM zV : Fin n ⊕ Fin 1 -> ℝ)
    (hBM :
      (Matrix.fromBlocks M
        (fun i (_ : Fin 1) => (a • k) i )
        (fun (_ : Fin 1) j => (a • k) j )
        (fun (_ _ : Fin 1) => V + r )).mulVec zM =
        Sum.elim u (fun _ : Fin 1 => ynew))
    (hBV :
      (Matrix.fromBlocks M
        (fun i (_ : Fin 1) => (a • k) i )
        (fun (_ : Fin 1) j => (a • k) j )
        (fun (_ _ : Fin 1) => V + r )).mulVec zV =
        Sum.elim (a • k) (fun _ : Fin 1 => V))
    (hS : (V + r) - ((a • k) ⬝ᵥ A.mulVec (a • k)) ≠ 0) :
    let pred : ℝ := a ^ 2 * Pold + V * (1 - a ^ 2)
    (((a • k) ⬝ᵥ (zM ∘ Sum.inl)) +
        V * zM (Sum.inr (0 : Fin 1)) =
      a * mold + pred / (pred + r) * (ynew - a * mold)) ∧
    (V - (((a • k) ⬝ᵥ (zV ∘ Sum.inl)) +
        V * zV (Sum.inr (0 : Fin 1))) =
      pred * r / (pred + r)) := by
  sorry
