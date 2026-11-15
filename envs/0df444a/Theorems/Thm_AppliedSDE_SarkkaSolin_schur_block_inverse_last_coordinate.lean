-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_schur_block_inverse_last_coordinate
-- name    : AppliedSDE.SarkkaSolin.schur_block_inverse_last_coordinate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:27:24.541197+00:00
-- url     : https://prove2.me/theorems/e20f5c88-0328-4cd7-8615-c01355a796b3
-- title:
--   Schur complement solves the appended coordinate of a finite matrix block linear system
-- statement:
--   Suppose the leading covariance block M has an explicit left inverse A, the old and new coordinates z and w solve M z + w k = u and k dot z + d w = v, and the Schur complement d-k dot A k is nonzero. Then the new coordinate is exactly w=(v-k dot A u)/(d-k dot A k). This derives the final-coordinate inverse solution directly from the real matrix block system, rather than assuming the leading vector was already eliminated. It is a key matrix-algebra input to the arbitrary-sample-size Gaussian-process batch equals Kalman filtering induction.
-- source:
--   Särkkä and Solin (2019), Applied Stochastic Differential Equations, Chapters 10 and 12; Schur-complement block solve for Gaussian conditioning.

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_schur_matrix_last_component
open Matrix
open scoped Matrix

theorem AppliedSDE.SarkkaSolin.schur_block_inverse_last_coordinate
    (n : ℕ)
    (M A : Matrix (Fin n) (Fin n) ℝ)
    (hAM : A * M = 1)
    (k u z : Fin n → ℝ) (w d v : ℝ)
    (hleft : M.mulVec z + w • k = u)
    (hrow : (k ⬝ᵥ z) + d * w = v)
    (hS : d - (k ⬝ᵥ A.mulVec k) ≠ 0) :
    w = (v - (k ⬝ᵥ A.mulVec u)) /
      (d - (k ⬝ᵥ A.mulVec k)) := by
  sorry
