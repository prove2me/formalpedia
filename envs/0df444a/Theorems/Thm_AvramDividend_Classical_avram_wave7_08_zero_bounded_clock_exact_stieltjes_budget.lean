-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_08_zero_bounded_clock_exact_stieltjes_budget
-- name    : AvramDividend.Classical.avram_wave7_08_zero_bounded_clock_exact_stieltjes_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T12:45:39.331208+00:00
-- url     : https://prove2.me/theorems/be98880d-3f6b-426e-8f4f-31ea29aad0e4
-- title:
--   Original corrected UBV exact n=0 bounded ruin-clock dividend Stieltjes bound
-- statement:
--   For the actual controlled spectrally negative Lévy source, the expected full discounted Stieltjes payout restricted to paymentTimes(min(ruinTime, 0)) and any nonnegative real horizon equals the exact time-zero payout, and is bounded by w(x) under the repaired boundary, gradient, admissibility, and initial jump hypotheses. This independently certifies the n=0 instance of the positive-reserve uniform bounded ruin-clock budget, without a stochastic Itô claim.
-- source:
--   Exact n=0 branch of Open original-source bounded ruin-clock target 3c9532b7-1071-4d95-b7a6-9279a240132f, using Proved corrected original-source time-zero bound 3858a86b-eff8-46f1-b700-7ee855dad85a. No change of Ω, P, X, D, paymentTimes, ruinTime, dividendMeasure or cap conventions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_08_zero_bounded_clock_exact_stieltjes_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (0 : ℝ≥0∞)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
