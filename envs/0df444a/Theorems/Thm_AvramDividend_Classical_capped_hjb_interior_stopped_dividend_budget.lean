-- Prove2me | Theorems.Thm_AvramDividend_Classical_capped_hjb_interior_stopped_dividend_budget
-- name    : AvramDividend.Classical.capped_hjb_interior_stopped_dividend_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T10:14:31.1145+00:00
-- url     : https://prove2.me/theorems/02509706-c707-49ca-a434-a6c41bc58ce7
-- title:
--   Nonpositive stopped HJB time-and-dividend budget on the strictly interior reserve region
-- statement:
--   Localise the genuine stopped dividend Stieltjes measure and the time measure to the positive reserve interior below the cap. The region condition required by the general HJB signed-budget theorem follows directly from membership in the localisation set. This isolates the boundary and zero-reserve times which a stochastic stopped change-of-variables proof must treat separately.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_capped_hjb_integrated_drift_dividend_residual_nonpos
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.capped_hjb_interior_stopped_dividend_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (σ : ℝ≥0∞) (T : ℝ≥0) (ω : Ω)
    (μtime : Measure ℝ) (u : ℝ → ℝ)
    (hInterior : MeasurableSet
      {t : ℝ | 0 < u t ∧ ENNReal.ofReal (u t) < C})
    (hTime : IntegrableOn (fun t : ℝ =>
      Real.exp (-(q * t)) * (X.generator w (u t) - q * w (u t)))
      ((paymentTimes σ ∩ Iic (T : ℝ)) ∩
      {t : ℝ | 0 < u t ∧ ENNReal.ofReal (u t) < C}) μtime)
    (hDiv : IntegrableOn (fun t : ℝ =>
      Real.exp (-(q * t)) * (1 - deriv w (u t)))
      ((paymentTimes σ ∩ Iic (T : ℝ)) ∩
      {t : ℝ | 0 < u t ∧ ENNReal.ofReal (u t) < C}) (dividendMeasure D ω)) :
    (∫ t in (paymentTimes σ ∩ Iic (T : ℝ)) ∩
      {t : ℝ | 0 < u t ∧ ENNReal.ofReal (u t) < C},
      Real.exp (-(q * t)) *
        (X.generator w (u t) - q * w (u t)) ∂μtime) +
    (∫ t in (paymentTimes σ ∩ Iic (T : ℝ)) ∩
      {t : ℝ | 0 < u t ∧ ENNReal.ofReal (u t) < C},
      Real.exp (-(q * t)) *
        (1 - deriv w (u t)) ∂(dividendMeasure D ω)) ≤ 0 := by sorry
