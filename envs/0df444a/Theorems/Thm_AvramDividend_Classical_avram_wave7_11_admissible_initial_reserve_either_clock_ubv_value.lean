-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_admissible_initial_reserve_either_clock_ubv_value
-- name    : AvramDividend.Classical.avram_wave7_11_admissible_initial_reserve_either_clock_ubv_value
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:49:01.887035+00:00
-- url     : https://prove2.me/theorems/05ca6c0b-4c63-4d81-983c-4f24c160eaf0
-- title:
--   Original UBV finite-horizon value with initial capital automatically nonnegative from capped admissibility
-- statement:
--   For a genuine admissible capped dividend strategy on the original spectrally negative Lévy law, cap membership and admissibility imply x≥0. Thus no separate initial-capital nonnegative assumption is needed in the corrected UBV finite-horizon source-value transfer. A positive-capital original stopped-cash budget can use either one future deterministic natural cutoff or one almost surely future random clock. No HJB or standing hypothesis is required for this deterministic conversion; the original source, ruin, discount and complete Stieltjes atoms are preserved.
-- source:
--   Proved all-cap original admissible initial-capital nonnegativity b3117b07 and Proved original-source minimal almost-surely future clock bridge 359d1ea2; a deterministic future natural clock is embedded as a constant random clock.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_allCap_admissible_initial_capital_nonneg
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_minimal_original_ubv_ae_clock_value_bridge
import Mathlib.Data.Real.Basic

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_admissible_initial_reserve_either_clock_ubv_value
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hw0 : 0 ≤ w 0)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T)
    (hEitherClock : 0 < x →
      (∃ n : ℕ, T < (n : ℝ) ∧
        (∫⁻ ω, ∫⁻ t in paymentTimes
          (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
          ENNReal.ofReal (w x)) ∨
      (∃ η : Ω → ℝ≥0∞,
        (∀ᵐ ω ∂P, ENNReal.ofReal T < η ω) ∧
        (∫⁻ ω, ∫⁻ t in paymentTimes
          (min (ruinTime X x D ω) (η ω)) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
          ENNReal.ofReal (w x))) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
