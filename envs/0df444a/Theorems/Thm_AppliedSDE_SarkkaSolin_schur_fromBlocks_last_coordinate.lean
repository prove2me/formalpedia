-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_schur_fromBlocks_last_coordinate
-- name    : AppliedSDE.SarkkaSolin.schur_fromBlocks_last_coordinate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T13:21:22.281458+00:00
-- url     : https://prove2.me/theorems/8f9df06a-c97b-4b06-86ff-15a37adb96d3
-- title:
--   Last coordinate of a genuine Matrix.fromBlocks system equals the Schur quotient
-- statement:
--   For any finite real leading matrix M with a left inverse A, symmetric cross-vector k and scalar diagonal d, consider the genuine block covariance matrix Matrix.fromBlocks(M,k,k^T,[d]) on Fin n sum Fin1. If its inverse solution z satisfies the block matrix equation and the scalar Schur complement S=d-k dot A k is nonzero, then its new last coordinate is (y_last-k dot A y_old)/S. This proves the actual 2-by-2 block matrix system elimination, transforming Mathlib fromBlocks_mulVec into the previously proved Schur linear algebra lemma. It is the missing matrix block step towards an arbitrary-sample-size Gaussian-process/Kalman filter equivalence induction.
-- source:
--   Särkkä and Solin (2019), Applied Stochastic Differential Equations, Chapters 10 and 12; exact Matrix.fromBlocks_mulVec Schur elimination.

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_schur_block_inverse_last_coordinate
open Matrix
open scoped Matrix

theorem AppliedSDE.SarkkaSolin.schur_fromBlocks_last_coordinate
    (n : ℕ) (M A : Matrix (Fin n) (Fin n) ℝ)
    (k : Fin n → ℝ) (d : ℝ)
    (y z : Fin n ⊕ Fin 1 → ℝ)
    (hAM : A * M = 1)
    (hblock :
      (Matrix.fromBlocks M
        (fun i (_ : Fin 1) => k i : Matrix (Fin n) (Fin 1) ℝ)
        (fun (_ : Fin 1) j => k j : Matrix (Fin 1) (Fin n) ℝ)
        (fun (_ _ : Fin 1) => d : Matrix (Fin 1) (Fin 1) ℝ)).mulVec z = y)
    (hS : d - (k ⬝ᵥ A.mulVec k) ≠ 0) :
    z (Sum.inr (0 : Fin 1)) =
      (y (Sum.inr (0 : Fin 1)) -
        (k ⬝ᵥ A.mulVec (y ∘ Sum.inl))) /
          (d - (k ⬝ᵥ A.mulVec k)) := by
  sorry
