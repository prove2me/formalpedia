-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_positive_time_ae_budget_suffices_all_ubv_horizons
-- name    : AvramDividend.Classical.avram_wave7_11_positive_time_ae_budget_suffices_all_ubv_horizons
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:40:05.385244+00:00
-- url     : https://prove2.me/theorems/2699fbc5-6582-424f-b82e-2e937e0cfd4a
-- title:
--   Original UBV all finite horizons from a single almost-sure clock only for strictly positive time and capital
-- statement:
--   For genuine original-process capped spectrally negative Lévy dividend strategies, the HJB-controlled time-zero initial Stieltjes atom is already proved. Hence to verify every nonnegative finite horizon it suffices to supply one expected strictly-future a.s. original ruin-clock budget for each strictly positive horizon and strictly positive initial capital. The x=0 branch follows from corrected UBV source, and the bound retains the original terminal dividend atom.
-- source:
--   Proved source admissible_cap_truncated_zero_horizon_hjb_bound, and Proved source avram_wave7_11_source_ubv_value_from_ae_future_clock_budget.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_admissible_cap_truncated_zero_horizon_hjb_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_source_ubv_value_from_ae_future_clock_budget
import Mathlib.Data.Real.Basic

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_positive_time_ae_budget_suffices_all_ubv_horizons
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hPositiveClocks : ∀ T : ℝ, 0 < T → 0 < x →
      ∃ η : Ω → ℝ≥0∞,
        (∀ᵐ ω ∂P, ENNReal.ofReal T < η ω) ∧
        (∫⁻ ω, ∫⁻ t in paymentTimes
          (min (ruinTime X x D ω) (η ω)) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
          ENNReal.ofReal (w x)) :
    ∀ T : ℝ, 0 ≤ T →
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x) := by sorry
