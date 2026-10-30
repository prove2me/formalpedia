-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_05_shifted_stopped_Ioc_discount_record_bounds_of_survival
-- name    : AvramDividend.Classical.avram_root29_05_shifted_stopped_Ioc_discount_record_bounds_of_survival
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T15:41:30.805034+00:00
-- url     : https://prove2.me/theorems/0b4e81ae-bec4-4fbe-817d-183ef7b76a1f
-- title:
--   Shifted future stopped Stieltjes interval bounds under survival
-- statement:
--   If a real half-open interval is entirely before the true strict shifted drawdown ruin clock, the actual future shifted supremum Stieltjes dividend integral with this stopping restriction is bracketed by the two endpoint-discount factors multiplied by the future record increment.
-- source:
--   Apply the accepted generic stopped-payment interval restriction lemma and the accepted shifted genuine Stieltjes q-discount endpoint bound; the argument keeps the exact shifted path, original Stieltjes measure and paymentTimes strict ruin set.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_lintegral_indicator_restrict_of_subset
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_shifted_qDiscount_Ioc_record_bounds

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-- Stopping removes no shifted Stieltjes dividend cash from a time interval
known entirely to precede the shifted strict-ruin clock. -/

theorem AvramDividend.Classical.avram_root29_05_shifted_stopped_Ioc_discount_record_bounds_of_survival
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (age : ℝ≥0)
    (τ : ℝ≥0∞) (q : ℝ) (hq : 0 ≤ q) (s t : ℝ)
    (hSurvive : Ioc s t ⊆ paymentTimes τ) :
    let M : ℝ≥0 → ℝ := fun v =>
      sSup ((fun w : ℝ≥0 => X.X (age + w) ω - X.X age ω) '' Icc 0 v)
    let μ : Measure ℝ := dividendMeasure (fun r (_ : Ω) => M r) ω
    (ENNReal.ofReal (Real.exp (-(q * t))) *
        ENNReal.ofReal (M t.toNNReal - M s.toNNReal) ≤
      ∫⁻ r in paymentTimes τ,
        if r ∈ Ioc s t then
          ENNReal.ofReal (Real.exp (-(q * r))) else 0 ∂μ) ∧
    ((∫⁻ r in paymentTimes τ,
        if r ∈ Ioc s t then
          ENNReal.ofReal (Real.exp (-(q * r))) else 0 ∂μ) ≤
      ENNReal.ofReal (Real.exp (-(q * s))) *
        ENNReal.ofReal (M t.toNNReal - M s.toNNReal)) := by sorry
