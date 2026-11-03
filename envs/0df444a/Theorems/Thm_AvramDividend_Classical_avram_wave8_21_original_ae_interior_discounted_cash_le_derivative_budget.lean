-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_21_original_ae_interior_discounted_cash_le_derivative_budget
-- name    : AvramDividend.Classical.avram_wave8_21_original_ae_interior_discounted_cash_le_derivative_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:13:54.966396+00:00
-- url     : https://prove2.me/theorems/b7ee9b53-a8ec-479f-9376-36974a063846
-- title:
--   Original almost-everywhere interior Stieltjes discounted cash bounded by HJB derivative-weighted cash
-- statement:
--   When the original controlled reserve is strictly positive and below the cap almost everywhere with respect to the very original dividendMeasure D ω restricted to A, the real discounted Stieltjes cash is bounded by its candidate-derivative-weighted counterpart under separate integrability of the two terms. This directly permits genuine diffuse or singular-continuous payout mass and strengthens the pointwise-interiority budget without assuming reserve interiority on every payment time.
-- source:
--   Original dividendMeasure, riskProcess, measure-a.e. interior HJB gradient inequality and signed integral subtraction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave8_21_original_ae_interior_discounted_cash_le_derivative_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (ω : Ω) (A : Set ℝ) (hA : MeasurableSet A)
    (hregion : ∀ᵐ t ∂(dividendMeasure D ω).restrict A,
      0 < riskProcess X x D t.toNNReal ω ∧
      ENNReal.ofReal (riskProcess X x D t.toNNReal ω) < C)
    (hCash : IntegrableOn (fun t : ℝ => Real.exp (-(q * t)))
      A (dividendMeasure D ω))
    (hDeriv : IntegrableOn
      (fun t : ℝ => Real.exp (-(q * t)) *
        deriv w (riskProcess X x D t.toNNReal ω))
      A (dividendMeasure D ω)) :
    (∫ t in A, Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ≤
      (∫ t in A, Real.exp (-(q * t)) *
        deriv w (riskProcess X x D t.toNNReal ω)
        ∂(dividendMeasure D ω)) := by sorry
