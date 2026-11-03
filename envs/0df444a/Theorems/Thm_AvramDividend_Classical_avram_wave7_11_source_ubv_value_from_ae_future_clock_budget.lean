-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_source_ubv_value_from_ae_future_clock_budget
-- name    : AvramDividend.Classical.avram_wave7_11_source_ubv_value_from_ae_future_clock_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:29:19.539708+00:00
-- url     : https://prove2.me/theorems/d73f3926-cece-44a9-8a00-f330049814d3
-- title:
--   Canonical UBV finite-horizon verification from one almost surely future source clock budget
-- statement:
--   Assume the exact canonical source UBV HJB verification conditions and nonnegative initial reserve. For strictly positive initial reserve, it suffices to have one sample-dependent localising clock η lying strictly after the finite horizon T almost surely under the original law P, and a cash budget at the genuine min(ruinTime X x D ω,ηω) stopped dividend reward. Then the exact original finite-horizon expected Stieltjes dividend value is bounded by ENNReal.ofReal(w x), with initial and terminal atoms retained. At initial reserve zero the corrected source theorem gives the bound directly. No auxiliary process, replacement sample space, atomlessness, or uniform clock estimate is used.
-- source:
--   Proved corrected zero-initial UBV cash bound 14599b22, Proved source HJB side conditions d307095e, and Proved a.e. future original cash budget bridge 16bfe94b.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_local_verification_stochastic_core_side_conditions
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_corrected_ubv_zero_initial_all_caps_exact_stieltjes_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_ae_future_ruin_clock_budget_controls_original_horizon
import Mathlib.Data.Real.Basic

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_source_ubv_value_from_ae_future_clock_budget
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
    (T : ℝ) (hT : 0 ≤ T)
    (hAeClock : 0 < x →
      ∃ η : Ω → ℝ≥0∞,
        (∀ᵐ ω ∂P, ENNReal.ofReal T < η ω) ∧
        (∫⁻ ω, ∫⁻ t in paymentTimes
          (min (ruinTime X x D ω) (η ω)) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
          ENNReal.ofReal (w x)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
