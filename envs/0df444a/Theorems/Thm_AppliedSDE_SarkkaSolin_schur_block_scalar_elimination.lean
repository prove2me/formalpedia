-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_schur_block_scalar_elimination
-- name    : AppliedSDE.SarkkaSolin.schur_block_scalar_elimination
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:51:34.335464+00:00
-- url     : https://prove2.me/theorems/00cc1540-646b-4672-8723-66bc8c7573f9
-- title:
--   Abstract Schur-complement last-coordinate formula for a block linear system
-- statement:
--   Let A be a real linear map representing the inverse action of a leading covariance block and l a real linear functional representing the cross-covariance row. If the leading-block unknown satisfies x=A(u-wb) and the last-row equation is l(x)+d w=v, then provided the Schur complement S=d-l(A b) is nonzero, the appended-coordinate solution is w=(v-l(Au))/S. This is the scalar elimination step of the block matrix inverse and is directly reusable when proving that Gaussian-process batch updates agree with Kalman filtering.
-- source:
--   Särkkä and Solin (2019), Applied Stochastic Differential Equations, Chapters 10 and 12; classical Schur-complement block solve.

import Mathlib

theorem AppliedSDE.SarkkaSolin.schur_block_scalar_elimination
    (n : ℕ)
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (l : (Fin n → ℝ) →ₗ[ℝ] ℝ)
    (u b x : Fin n → ℝ) (w d v : ℝ)
    (hx : x = A (u - w • b))
    (hrow : l x + d * w = v)
    (hS : d - l (A b) ≠ 0) :
    w = (v - l (A u)) / (d - l (A b)) := by
  sorry
