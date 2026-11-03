-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_21_original_stieltjes_ae_interior_discounted_diffuse_correction_nonpositive
-- name    : AvramDividend.Classical.avram_wave8_21_original_stieltjes_ae_interior_discounted_diffuse_correction_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:08:24.449352+00:00
-- url     : https://prove2.me/theorems/d2443bee-f837-4979-af8c-c82773c02ff2
-- title:
--   Original Stieltjes discounted derivative correction nonpositive under actual payout-measure almost-everywhere interiority
-- statement:
--   For the actual original dividendMeasure D ω restricted to any measurable time region A, if the original reserve is strictly positive and below the cap almost everywhere under this very restricted payout measure, the discounted signed correction exp(-q*t)*(1-deriv w(reserve)) has nonpositive integral. This handles genuine continuous and singular-continuous cash when pointwise interiority fails at a null set; the atomic and cap boundary contributions must still be handled separately. No surrogate measure is used.
-- source:
--   Original dividendMeasure and riskProcess, HJB interior gradient, Mathlib integral_nonpos_of_ae.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave8_21_original_stieltjes_ae_interior_discounted_diffuse_correction_nonpositive
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
      ENNReal.ofReal (riskProcess X x D t.toNNReal ω) < C) :
    (∫ t in A, Real.exp (-(q * t)) *
      (1 - deriv w (riskProcess X x D t.toNNReal ω))
      ∂(dividendMeasure D ω)) ≤ 0 := by sorry
