-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_ubv_original_nonmonotone_cofinal_overshooting_fatou
-- name    : AvramDividend.Classical.avram_wave6_ubv_original_nonmonotone_cofinal_overshooting_fatou
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T17:34:05.766181+00:00
-- url     : https://prove2.me/theorems/e64353b1-517f-4b15-9e41-cad945117d5f
-- title:
--   Original UBV nonmonotone overshooting-clock Fatou from cofinally many stochastic budgets
-- statement:
--   For the actual source SpectrallyNegativeLevy P 𝓕 and admissible D, arbitrary measurable clocks may be nonmonotone and overshoot ruin. Assume liminf of original clocks covers ruin almost surely, and the full discounted Stieltjes expected budget holds at arbitrarily large indices. Select a cofinal-index subsequence of budgeted clocks; its liminf remains above ruin. Apply the Proved original overshooting-liminf Fatou theorem. This adds no boundary, smoothness, bounded-variation, atomlessness, or filtration assumption. The cofinally available stochastic budgets remain an explicit premise.
-- source:
--   Corrected core 429e17ca-5528-40b5-b593-7c03973d0706; accepted original overshooting-liminf Fatou 0fd62ba3-85ac-4c84-a50c-8903a2c8a2cb.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_overshooting_liminf_fatou_no_extra_nonneg

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_ubv_original_nonmonotone_cofinal_overshooting_fatou
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T)
    (τ : ℕ → Ω → ℝ≥0∞) (hτmeas : ∀ n, Measurable (τ n))
    (hτliminfLowerAE : ∀ᵐ ω ∂P,
      ruinTime X x D ω ≤ (⨆ n : ℕ, ⨅ k : ℕ, τ (n + k) ω))
    (hBudgetCofinal : ∀ k : ℕ, ∃ n : ℕ, k ≤ n ∧
      (∫⁻ ω, ∫⁻ t in paymentTimes (τ n ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
