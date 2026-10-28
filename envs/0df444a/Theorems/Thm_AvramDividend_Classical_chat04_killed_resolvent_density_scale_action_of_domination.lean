-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_killed_resolvent_density_scale_action_of_domination
-- name    : AvramDividend.Classical.chat04_killed_resolvent_density_scale_action_of_domination
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:43:16.290504+00:00
-- url     : https://prove2.me/theorems/91790147-d431-4dd1-9819-1a39527c3de0
-- title:
--   Killed-resolvent scale action from one integrable Laplace term
-- statement:
--   The explicit killed-resolvent spatial kernel integrates against the q-scale function to W_q(x)/p under tilted-scale monotonicity, a single integrable Laplace term and measurability. Positivity of the spatial kernel supplies domination and hence automatically gives integrability of the convolution.
-- source:
--   Combination of remotely verified full-halfline spatial kernel positivity, scale convolution identity and Mathlib integral domination.

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Theorems.Thm_AvramDividend_Classical_chat04_killed_resolvent_kernel_nonneg_full_halfline
import Theorems.Thm_AvramDividend_Classical_chat04_killed_resolvent_density_scale_action_of_integrable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_killed_resolvent_density_scale_action_of_domination
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q p θ : ℝ) (hq : 0 ≤ q) (hp : 0 < p)
    (hθ : 0 ≤ θ) (hroot : X.ψ θ = q + p)
    (Wq Wqp : ℝ → ℝ)
    (hWq : IsScaleFunction X q Wq)
    (hWqp : IsScaleFunction X (q + p) Wqp)
    (hmono : MonotoneOn
      (fun z : ℝ => Real.exp (-(θ * z)) * Wqp z) (Ici (0 : ℝ)))
    (hWq_nonneg : ∀ z : ℝ, 0 ≤ z → 0 ≤ Wq z)
    (hWqp_nonneg : ∀ z : ℝ, 0 ≤ Wqp z)
    (hnegative : ∀ z : ℝ, z < 0 → Wqp z = 0)
    (x : ℝ) (hx : 0 < x)
    (hfirst : IntegrableOn
      (fun y : ℝ => Wq y * (Real.exp (-(θ * y)) * Wqp x))
      (Ioi (0 : ℝ)))
    (hmeas : AEStronglyMeasurable
      (fun y : ℝ => Wq y * Wqp (x - y))
      (volume.restrict (Ioi (0 : ℝ)))) :
    (∫ y in Ioi (0 : ℝ),
      Wq y * (Real.exp (-(θ * y)) * Wqp x - Wqp (x - y))) =
    Wq x / p := by sorry
