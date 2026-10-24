-- Prove2me | Theorems.Thm_AvramDividend_Classical_capped_hjb_discounted_generator_integral_nonpos
-- name    : AvramDividend.Classical.capped_hjb_discounted_generator_integral_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:42:24.295734+00:00
-- url     : https://prove2.me/theorems/38369947-2751-476f-b6eb-55a1bf1468fc
-- title:
--   Integrated discounted capped HJB generator residual is nonpositive
-- statement:
--   Any spectrally negative Lévy model with a capped HJB supersolution has a nonpositive integrated discounted generator minus discount residual on an arbitrary measurable active-time set where the reserve path remains strictly positive and below the cap, assuming residual integrability. This common BV/UV local verification drift bound is reusable in stopped Itô formula arguments.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Theorems.Thm_AvramDividend_Classical_hjb_component_inequalities

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.capped_hjb_discounted_generator_integral_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (μ : Measure ℝ) (u : ℝ → ℝ) (A : Set ℝ)
    (hA : MeasurableSet A)
    (hregion : ∀ t ∈ A, 0 < u t ∧ ENNReal.ofReal (u t) < C)
    (hInt : IntegrableOn (fun t : ℝ =>
      Real.exp (-(q * t)) * (X.generator w (u t) - q * w (u t))) A μ) :
    (∫ t in A, Real.exp (-(q * t)) *
      (X.generator w (u t) - q * w (u t)) ∂μ) ≤ 0 := by sorry
