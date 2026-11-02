-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_ae_monotone_rightcont_stopping_fatou_no_extra_nonneg
-- name    : AvramDividend.Classical.avram_wave5_ubv_original_ae_monotone_rightcont_stopping_fatou_no_extra_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:01:36.867255+00:00
-- url     : https://prove2.me/theorems/cfe20bf7-0076-45f3-839e-8bf60af567ca
-- title:
--   Source right-continuous localising stopping clocks: Fatou with both monotonicity and cofinality almost sure
-- statement:
--   With the actual spectrally negative Levy source and admissible D, and genuine right-continuous-filtration stopping times S_n, the a.s. monotone and a.s. cofinal stopping clocks S_n↑∞ yield the full expected discounted dividend reward bound from a uniform budget at min(ruinTime,S_n). Neither global pathwise monotonicity nor pathwise cofinality is needed. The uniform budget is still explicit, no controlled Ito-Meyer or Stieltjes work is duplicated, and no extra boundary or smoothness hypotheses are introduced.
-- source:
--   Corrected core 429e17ca-5528-40b5-b593-7c03973d0706; Proved ruinTime stopping 0df48030-cd88-4a84-a1f0-f2d1ed6e13ee; source almost-sure monotonicity Fatou bridge dependent theorem to be published. No core or milestone mutation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_ae_monotone_ae_cofinal_fatou_no_extra_nonneg

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_ubv_original_ae_monotone_rightcont_stopping_fatou_no_extra_nonneg
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
    (S : ℕ → Ω → ℝ≥0∞)
    (hSstop : ∀ n, IsStoppingTime 𝓕.rightCont (S n))
    (hSmonoAE : ∀ᵐ ω ∂P, Monotone (fun n => S n ω))
    (hSsupAE : ∀ᵐ ω ∂P, (⨆ n, S n ω) = ⊤)
    (hBudget : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (S n ω)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
