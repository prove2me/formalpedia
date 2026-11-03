-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_08_zero_clock_source_dividend_budget
-- name    : AvramDividend.Classical.avram_wave7_08_zero_clock_source_dividend_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:54:27.309111+00:00
-- url     : https://prove2.me/theorems/495136c2-f564-4e70-b879-448d5d444a3d
-- title:
--   Original UBV zero-truncated source clock dividend bound from corrected time-zero secant
-- statement:
--   For any observation horizon T, if the genuine source ruin clock is truncated at n=0, its cash cannot exceed the corrected time-zero bound with w(0)≥0. This follows from original paymentTimes set inclusion and the Proved corrected zero-horizon stochastic estimate, preserving the initial atom.
-- source:
--   Consumes Proved avram_wave3_04_corrected_ubv_zero_horizon_bound and newly published avram_wave7_08_zero_clock_paymentTimes_sub_source_zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_08_zero_clock_source_dividend_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (0 : ℝ≥0∞)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
