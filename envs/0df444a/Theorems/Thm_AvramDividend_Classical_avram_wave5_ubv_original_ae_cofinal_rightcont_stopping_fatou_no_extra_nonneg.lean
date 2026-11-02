-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_ae_cofinal_rightcont_stopping_fatou_no_extra_nonneg
-- name    : AvramDividend.Classical.avram_wave5_ubv_original_ae_cofinal_rightcont_stopping_fatou_no_extra_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:36:59.732902+00:00
-- url     : https://prove2.me/theorems/50f1ac14-ee37-4ba4-8422-16a91069d854
-- title:
--   Same-source UBV full ruin-clock Fatou from almost-surely cofinal genuine right-continuous stochastic localisers
-- statement:
--   For the actual SpectrallyNegativeLevy P 𝓕, its true admissible strategy D, and arbitrary original right-continuous-filtration stopping localisers S_n which increase pathwise and tend to infinity P-almost surely (not necessarily on exceptional null paths), the full discounted Stieltjes reward at genuine ruin follows from a uniform budget at each actual min(ruinTime,S_n) stopped clock. This applies in particular to bounded stochastic localisers. No new w boundary or cap conditions, no finite-variation or no-creeping assumptions. It is a clock-and-Fatou handoff, not an independent Stieltjes or controlled Ito-Meyer estimate; hBudget remains explicit.
-- source:
--   Corrected core 429e17ca-5528-40b5-b593-7c03973d0706; reuse Proved right-continuous ruinTime stopping 2d036d4f-57b5-4b28-864b-a2ff5082e323 and P2M ae cofinal Fatou 8461667e-15cd-4077-8bd2-ce40dbc6734d (pending proof verdict at drafting). Do not modify target or milestones.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_ae_cofinal_stochastic_fatou_no_extra_nonneg

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_ubv_original_ae_cofinal_rightcont_stopping_fatou_no_extra_nonneg
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
    (hSmono : ∀ ω, Monotone (fun n => S n ω))
    (hSsupAE : ∀ᵐ ω ∂P, (⨆ n, S n ω) = ⊤)
    (hBudget : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (S n ω)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
