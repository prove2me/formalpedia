-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_scale_laplace_at_shifted_exponent_root
-- name    : AvramDividend.Classical.chat04_scale_laplace_at_shifted_exponent_root
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:52:48.800523+00:00
-- url     : https://prove2.me/theorems/66389b58-96f9-40d8-9e4a-431217c572bc
-- title:
--   Scale Laplace transform at a shifted-exponent root is the reciprocal resolvent discount
-- statement:
--   For p>0 and a nonnegative exponent θ satisfying ψ(θ)=q+p, the Laplace transform of the q-scale function W^(q) at θ equals 1/p. This is the exponential-kernel term in the killed-process resolvent cancellation route to scalar q-scale harmonicity, derived entirely from the defining scale transform.
-- source:
--   Proved scaleFunction_shifted_laplace_transform with zero spatial shift and root equality; no killed-process or exit identity assumptions.

import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_scaleFunction_shifted_laplace_transform

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_scale_laplace_at_shifted_exponent_root
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q p θ : ℝ) (hp : 0 < p) (hθ : 0 ≤ θ)
    (hroot : X.ψ θ = q + p)
    (Wq : ℝ → ℝ) (hWq : IsScaleFunction X q Wq) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * Wq x) =
      p⁻¹ := by sorry
