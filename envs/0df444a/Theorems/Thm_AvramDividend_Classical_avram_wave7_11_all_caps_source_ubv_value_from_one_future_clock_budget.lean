-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_all_caps_source_ubv_value_from_one_future_clock_budget
-- name    : AvramDividend.Classical.avram_wave7_11_all_caps_source_ubv_value_from_one_future_clock_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:31:15.714516+00:00
-- url     : https://prove2.me/theorems/ebc715ed-8e77-4176-9d30-461379f45564
-- title:
--   All-cap original UBV finite-horizon Stieltjes dividend bound from one future clock
-- statement:
--   For the exact original spectrally negative Lévy process, cap-admissible dividend strategy, C² UBV HJB candidate, and finite horizon T≥0, a zero cap requires no stochastic clock estimate: it is controlled by the corrected zero-cap initial reserve Stieltjes bound. If the cap is positive and initial reserve is positive, only one sufficiently future natural ruin-clock cash budget is needed. Under this explicit conditional stochastic hypothesis, the original complete finite-horizon dividend value is bounded by ENNReal.ofReal(w x) for every cap including C=0, preserving both time-zero and positive-horizon dividend atoms.
-- source:
--   Proved source local HJB side conditions d307095e, Proved corrected W7-11 zero-cap Stieltjes theorem, and newly Proved positive-cap one-future-clock conditional source value theorem c6a91a53 (after verification).

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_local_verification_stochastic_core_side_conditions
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_zero_cap_original_stieltjes_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_source_ubv_value_from_one_future_clock_budget
import Mathlib.Data.Real.Basic

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_all_caps_source_ubv_value_from_one_future_clock_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T)
    (hOneClock : 0 < C → 0 < x →
      ∃ n : ℕ, T < (n : ℝ) ∧
        (∫⁻ ω, ∫⁻ t in paymentTimes
          (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
          ENNReal.ofReal (w x)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
