-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_schur_fromBlocks_covariance_posterior_variance
-- name    : AppliedSDE.SarkkaSolin.schur_fromBlocks_covariance_posterior_variance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T13:46:01.195931+00:00
-- url     : https://prove2.me/theorems/1a7fc9dd-4d51-4f21-b990-fefd36e14543
-- title:
--   Covariance posterior variance from the Schur block-system last coordinate
-- statement:
--   For a finite symmetric block covariance system with leading block M admitting left inverse A, block cross-covariance b and final diagonal V+r, solve the system for the covariance last-column vector with right-hand side (b,V). Provided the scalar Schur complement is nonzero, the final posterior variance V minus the covariance-vector inner product against the solution is exactly r times the Schur predicted variance divided by the innovation denominator. This generic lemma isolates the matrix step in the arbitrary-n AR(1) Gaussian-process versus Kalman variance induction.
-- source:
--   Sarkka and Solin (2019), Applied Stochastic Differential Equations, Gaussian process filtering and Kalman conditioning, Chapters 10 and 12.

import Mathlib
open Matrix
open scoped Matrix

theorem AppliedSDE.SarkkaSolin.schur_fromBlocks_covariance_posterior_variance
    (n : ℕ) (M A : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n -> ℝ) (V r : ℝ)
    (z : Fin n ⊕ Fin 1 -> ℝ)
    (hAM : A * M = 1)
    (hblock :
      (Matrix.fromBlocks M
        (fun i (_ : Fin 1) => b i )
        (fun (_ : Fin 1) j => b j )
        (fun (_ _ : Fin 1) => V + r )).mulVec z =
        Sum.elim b (fun _ : Fin 1 => V))
    (hS : (V + r) - (b ⬝ᵥ A.mulVec b) ≠ 0) :
    V - ((b ⬝ᵥ (z ∘ Sum.inl)) + V * z (Sum.inr (0 : Fin 1))) =
      (V - (b ⬝ᵥ A.mulVec b)) * r /
        ((V + r) - (b ⬝ᵥ A.mulVec b)) := by
  sorry
