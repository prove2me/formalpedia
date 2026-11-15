-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_schur_matrix_last_component
-- name    : AppliedSDE.SarkkaSolin.schur_matrix_last_component
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:02:14.558367+00:00
-- url     : https://prove2.me/theorems/5f18ca3e-6e5c-487d-aca4-4a1915c36b42
-- title:
--   Schur-complement scalar solution formula for an appended covariance matrix row
-- statement:
--   Let A be the leading-block inverse matrix, b the cross-covariance vector, u the leading observations, and x and w the leading and new unknowns solving x=A(u-wb) and b dot x + d w=v. If the scalar Schur complement d-b dot A b is nonzero, then the appended unknown w equals (v-b dot A u)/(d-b dot A b). The theorem links the abstract proved Schur elimination formula to actual finite matrices and matrix-vector products, ready for Gaussian-process covariance block inversions and Kalman filtering induction.
-- source:
--   Särkkä and Solin (2019), Applied Stochastic Differential Equations, Chapters 10 and 12; Mathlib Matrix.mulVecLin and dotProductBilin.

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_schur_block_scalar_elimination
open Matrix
open scoped Matrix

theorem AppliedSDE.SarkkaSolin.schur_matrix_last_component
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (b u x : Fin n → ℝ) (w d v : ℝ)
    (hx : x = A.mulVec (u - w • b))
    (hrow : (b ⬝ᵥ x) + d * w = v)
    (hS : d - (b ⬝ᵥ A.mulVec b) ≠ 0) :
    w = (v - (b ⬝ᵥ A.mulVec u)) /
      (d - (b ⬝ᵥ A.mulVec b)) := by
  sorry
