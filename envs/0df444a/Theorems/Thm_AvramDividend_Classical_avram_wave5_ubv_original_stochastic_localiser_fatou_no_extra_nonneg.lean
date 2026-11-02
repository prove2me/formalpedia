-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_stochastic_localiser_fatou_no_extra_nonneg
-- name    : AvramDividend.Classical.avram_wave5_ubv_original_stochastic_localiser_fatou_no_extra_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:03:56.214954+00:00
-- url     : https://prove2.me/theorems/d67458f5-21f6-40e8-aa04-4460fa861512
-- title:
--   Actual source stochastic-localiser Fatou with gradient-derived nonnegative terminal candidates
-- statement:
--   For the exact corrected UBV source X and admissible dividend strategy D, arbitrary cofinal increasing stopping times S n in the original right-continuous source filtration give ruin-stopped measurable increasing clocks. Uniform verified bounded stochastic-localiser dividend budgets then imply the full ruin-time expected dividend budget by the already Proved Fatou passage. The corrected core's separate pre-ruin nonnegative-value hypothesis is discharged from 0 ≤ w 0, continuous-on-nonnegative reserves and its existing gradient/C2 assumptions by the accepted original-path theorem. No new smoothness, boundary, bounded-variation, horizon, or filtration conditions are imposed. This is only a clock/nonnegativity/Fatou transfer; stochastic localised budgets themselves remain an explicit hypothesis, assigned to the separate controlled Itô–Meyer and dividend Stieltjes researchers.
-- source:
--   Corrected core 429e17ca-5528-40b5-b593-7c03973d0706; Proved nonnegative candidate a81e26e3-b329-4cf1-bd1f-7ce8d83fd66b; Proved genuine original localiser clocks 0df48030-cd88-4a84-a1f0-f2d1ed6e13ee; Proved stopped-clock Fatou 974b727e-2e1d-4045-906b-c28640b64eed. No core or milestone modification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_preruin_candidate_nonnegative_from_gradient
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_original_stopped_martingale_localiser_clocks
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_corrected_ubv_from_uniform_stopped_budget

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_ubv_original_stochastic_localiser_fatou_no_extra_nonneg
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
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
    (hSsup : ∀ ω, (⨆ n, S n ω) = ⊤)
    (hBudget : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (S n ω)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
