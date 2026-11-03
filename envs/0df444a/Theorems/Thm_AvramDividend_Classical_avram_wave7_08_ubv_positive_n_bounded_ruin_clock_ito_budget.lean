-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_08_ubv_positive_n_bounded_ruin_clock_ito_budget
-- name    : AvramDividend.Classical.avram_wave7_08_ubv_positive_n_bounded_ruin_clock_ito_budget
-- status  : Open
-- author  : @WillR
-- created : 2026-11-02T12:57:42.420581+00:00
-- url     : https://prove2.me/theorems/665b3b52-1f20-4307-8905-5b429a0f6425
-- title:
--   Corrected UBV original source bounded ruin-clock Ito-Meyer budget for positive natural clocks
-- statement:
--   At strictly positive starting reserve and every strictly positive natural bounded ruin clock n, the exact original source stopped finite-horizon discounted Stieltjes dividend inequality follows from the corrected UBV HJB generator, derivative and jump assumptions. Unlike the n=0 branch, this needs genuine stopped mixed Gaussian/negative-jump Ito-Meyer with exact source martingale and ruin-boundary control.
-- source:
--   Source-faithful n>0 branch of Open bounded original ruin-clock theorem 3c9532b7-1071-4d95-b7a6-9279a240132f; the n=0 branch is independently Proved by be98880d-3f6b-426e-8f4f-31ea29aad0e4. This publication by itself is only an Open mathematical obligation, not a proof of the parent.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_08_ubv_positive_n_bounded_ruin_clock_ito_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T)
    (n : ℕ) (hn : 0 < n) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
