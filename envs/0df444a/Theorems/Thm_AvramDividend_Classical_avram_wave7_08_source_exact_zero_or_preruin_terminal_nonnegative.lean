-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_exact_zero_or_preruin_terminal_nonnegative
-- name    : AvramDividend.Classical.avram_wave7_08_source_exact_zero_or_preruin_terminal_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:25:12.97711+00:00
-- url     : https://prove2.me/theorems/18481770-470e-430e-9858-98102f0feeca
-- title:
--   Nonnegative original UBV terminal term at exact zero-or-strict-pre-ruin stopped reserve
-- statement:
--   For original-source UBV x>0 and w(0)≥0, prove the discounted terminal reward is nonnegative almost everywhere at any stopped piecewise postpayment reserve, including the distinct τ=0 right-dividend-atom branch. Uses the Proved exact zero-or-strict source terminal sign theorem with its BV branch discharged vacuously by ¬BoundedVariation. No jump martingale is asserted.
-- source:
--   Corollary of Proved 9bd8e442-85b4-48e7-9612-878113303984, directly matches W and Term in canonical f8445859 and MGH child 0dda1be7.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_08_source_exact_zero_or_preruin_terminal_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (W Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) :
    ∀ᵐ ω ∂P, 0 ≤ Term ω := by sorry
