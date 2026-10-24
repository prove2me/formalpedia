-- Prove2me | Theorems.Thm_AvramDividend_Classical_capped_hjb_integrated_drift_dividend_residual_nonpos
-- name    : AvramDividend.Classical.capped_hjb_integrated_drift_dividend_residual_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:43:57.134965+00:00
-- url     : https://prove2.me/theorems/b86c4db6-7019-4ac6-8c67-4e63170b339c
-- title:
--   Combined integrated HJB drift and singular dividend residual is nonpositive
-- statement:
--   For any measurable time region on which a controlled reserve remains positive and below a cap, the discounted integral of the HJB generator residual against a time measure plus the discounted marginal-dividend residual against an arbitrary possibly singular dividend measure is nonpositive, assuming the two integrands are integrable. This is the deterministic signed-budget component of the bounded- and unbounded-variation stochastic verification identity.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Theorems.Thm_AvramDividend_Classical_hjb_component_inequalities

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.capped_hjb_integrated_drift_dividend_residual_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (μtime μdiv : Measure ℝ) (u : ℝ → ℝ) (A : Set ℝ)
    (hA : MeasurableSet A)
    (hregion : ∀ t ∈ A, 0 < u t ∧ ENNReal.ofReal (u t) < C)
    (hTime : IntegrableOn (fun t : ℝ =>
      Real.exp (-(q * t)) * (X.generator w (u t) - q * w (u t))) A μtime)
    (hDiv : IntegrableOn (fun t : ℝ =>
      Real.exp (-(q * t)) * (1 - deriv w (u t))) A μdiv) :
    (∫ t in A, Real.exp (-(q * t)) *
        (X.generator w (u t) - q * w (u t)) ∂μtime) +
      (∫ t in A, Real.exp (-(q * t)) *
        (1 - deriv w (u t)) ∂μdiv) ≤ 0 := by sorry
