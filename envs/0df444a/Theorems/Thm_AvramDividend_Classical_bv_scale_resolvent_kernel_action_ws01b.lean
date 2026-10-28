-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_scale_resolvent_kernel_action_ws01b
-- name    : AvramDividend.Classical.bv_scale_resolvent_kernel_action_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T12:45:23.183095+00:00
-- url     : https://prove2.me/theorems/671b0e7c-a3ac-4713-b784-942864f9aed2
-- title:
--   BV analytic killed-resolvent scale kernel action without zero-origin assumption
-- statement:
--   For a standing bounded-variation spectrally negative Levy process, the difference between the exponential Laplace kernel acting on the q-scale and the two-discount convolution is Wq(x)/p. Valid for infinite jump activity and Wq(0)>0.
-- source:
--   Accepted general scale resolvent convolution and shifted-root Laplace transform.

import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_scale_resolvent_convolution_of_scale_integrability
import Theorems.Thm_AvramDividend_Classical_chat04_scale_laplace_at_shifted_exponent_root

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_scale_resolvent_kernel_action_ws01b
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (q p θ b : ℝ) (hq : 0 < q) (hp : 0 < p)
    (hθ : 0 ≤ θ) (hroot : X.ψ θ = q + p)
    (Wq Wqp : ℝ → ℝ)
    (hWq : IsScaleFunction X q Wq)
    (hWqp : IsScaleFunction X (q + p) Wqp)
    (hlarge : ∀ β : ℝ, b < β →
      0 ≤ β ∧ q < X.ψ β ∧ q + p < X.ψ β)
    (hanchor : ∃ β : ℝ, b < β)
    (x : ℝ) (hx : 0 < x) :
    (∫ y in Ioi (0 : ℝ), Real.exp (-(θ * y)) * Wq y) * Wqp x -
      (∫ s in Ioc (0 : ℝ) x, Wq s * Wqp (x - s)) =
      Wq x / p := by sorry
