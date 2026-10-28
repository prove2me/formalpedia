-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_killed_resolvent_density_scale_action_of_integrable
-- name    : AvramDividend.Classical.chat04_killed_resolvent_density_scale_action_of_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T07:20:25.430829+00:00
-- url     : https://prove2.me/theorems/34efb710-e219-4148-a5a3-a178bce547ec
-- title:
--   Killed-resolvent density integrates against the scale function to give the scale value divided by the rate
-- statement:
--   For an unbounded-variation spectrally negative Lévy process, the explicit killed-resolvent spatial kernel exp(-Phi(q+p)y) W_(q+p)(x) minus W_(q+p)(x-y), integrated against W_q(y) on the positive half-line, equals W_q(x)/p. The hypotheses specify integrability of both constituent terms. This directly connects the verified convolution identity to the form required for the killed-resolvent density formula.
-- source:
--   Algebraic reformulation of the previously verified full-half-line scale resolvent kernel action.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_halfline_scale_resolvent_kernel_action

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_killed_resolvent_density_scale_action_of_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q p θ : ℝ) (hq : 0 ≤ q) (hp : 0 < p)
    (hθ : 0 ≤ θ) (hroot : X.ψ θ = q + p)
    (Wq Wqp : ℝ → ℝ)
    (hWq : IsScaleFunction X q Wq)
    (hWqp : IsScaleFunction X (q + p) Wqp)
    (hzero : ∀ z : ℝ, z < 0 → Wqp z = 0)
    (x : ℝ) (hx : 0 < x)
    (hfirst : IntegrableOn
      (fun y : ℝ => Wq y * (Real.exp (-(θ * y)) * Wqp x))
      (Ioi (0 : ℝ)))
    (hsecond : IntegrableOn
      (fun y : ℝ => Wq y * Wqp (x - y))
      (Ioi (0 : ℝ))) :
    (∫ y in Ioi (0 : ℝ),
      Wq y * (Real.exp (-(θ * y)) * Wqp x - Wqp (x - y))) =
    Wq x / p := by sorry
