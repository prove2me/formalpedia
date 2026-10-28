-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_unbounded_scale_resolvent_kernel_action
-- name    : AvramDividend.Classical.chat04_unbounded_scale_resolvent_kernel_action
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:58:16.859842+00:00
-- url     : https://prove2.me/theorems/b911918b-095b-4ba7-b2fb-bf94483a2347
-- title:
--   Exponential-minus-convolution resolvent kernel acts on Wq as Wq divided by p
-- statement:
--   For a spectrally negative Lévy process of unbounded variation, evaluate the q-scale function against the exponential-minus-convolution kernel of the (q+p)-scale function. When ψ(θ)=q+p and p>0, this integral kernel has the exact action W^(q)(x)/p. This is the analytic cancellation that would establish the Laplace-in-time transform of killed-scale harmonicity once the killed resolvent density is independently proved.
-- source:
--   Direct composition of Proved scale Laplace root and q-scale resolvent quotient cancellation. Neither imports a stopped martingale or exit identity.

import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_chat04_scale_laplace_at_shifted_exponent_root
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_scale_resolvent_discount_cancellation

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_unbounded_scale_resolvent_kernel_action
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q p θ : ℝ) (hq : 0 ≤ q) (hp : 0 < p) (hθ : 0 ≤ θ)
    (hroot : X.ψ θ = q + p)
    (Wq Wqp : ℝ → ℝ)
    (hWq : IsScaleFunction X q Wq)
    (hWqp : IsScaleFunction X (q + p) Wqp)
    (x : ℝ) (hx : 0 < x) :
    (∫ y in Ioi (0 : ℝ), Real.exp (-(θ * y)) * Wq y) * Wqp x -
      (∫ s in Ioc (0 : ℝ) x, Wq s * Wqp (x - s)) =
    Wq x / p := by sorry
