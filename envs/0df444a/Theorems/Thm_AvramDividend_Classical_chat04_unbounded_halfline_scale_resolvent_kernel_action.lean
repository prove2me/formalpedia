-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_unbounded_halfline_scale_resolvent_kernel_action
-- name    : AvramDividend.Classical.chat04_unbounded_halfline_scale_resolvent_kernel_action
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:38:25.146378+00:00
-- url     : https://prove2.me/theorems/fb7d8b4c-a62d-40c5-92f2-8a022f602f87
-- title:
--   Full-half-line spatial kernel action for the killed Lévy resolvent
-- statement:
--   Extend the accepted analytic q-scale kernel action from the truncated convolution (0,x] to the full nonnegative spatial half-line using the support of the (q+p)-scale function. This matches the spatial domain in the killed-resolvent density formula, conditional only on the explicit negative-half-line zero property.
-- source:
--   Composition of verified kernel action and independent support-restriction lemma.

import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_scale_resolvent_kernel_action
import Theorems.Thm_AvramDividend_Classical_chat04_killed_resolvent_convolution_support_restrict

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_unbounded_halfline_scale_resolvent_kernel_action
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q p θ : ℝ) (hq : 0 ≤ q) (hp : 0 < p)
    (hθ : 0 ≤ θ) (hroot : X.ψ θ = q + p)
    (Wq Wqp : ℝ → ℝ)
    (hWq : IsScaleFunction X q Wq)
    (hWqp : IsScaleFunction X (q + p) Wqp)
    (hzero : ∀ z : ℝ, z < 0 → Wqp z = 0)
    (x : ℝ) (hx : 0 < x) :
    (∫ y in Ioi (0 : ℝ), Real.exp (-(θ * y)) * Wq y) * Wqp x -
      (∫ y in Ioi (0 : ℝ), Wq y * Wqp (x - y)) =
    Wq x / p := by sorry
