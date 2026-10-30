-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_05_shifted_qDiscount_Ioc_record_bounds
-- name    : AvramDividend.Classical.avram_root29_05_shifted_qDiscount_Ioc_record_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T15:37:18.549631+00:00
-- url     : https://prove2.me/theorems/45d60fa0-c709-43fc-b028-8a752e4c74c7
-- title:
--   Shifted genuine Lévy regulator interval discount bounds
-- statement:
--   For any original spectrally negative Lévy sample path, age shift, nonnegative discount rate and real interval, its actual shifted supremum Stieltjes measure's discounted Ioc cash integral is between endpoint discount factors times the true shifted future-record increment. No future-only distribution is asserted.
-- source:
--   Antitone q-discount and monotonicity of the nonnegative Lebesgue integral bracket the interval reward between constant endpoint weights, and the Proved shifted Stieltjes interval-mass identity converts both constants to genuine shifted record increments.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_shiftedSup_stieltjes_Ioc_eq_record_increment

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-- Endpoint discount bounds for the genuine Stieltjes cash measure
of any finite-age shifted Lévy future running supremum. -/

theorem AvramDividend.Classical.avram_root29_05_shifted_qDiscount_Ioc_record_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (age : ℝ≥0) (q : ℝ) (hq : 0 ≤ q) (s t : ℝ) :
    let M : ℝ≥0 → ℝ := fun v =>
      sSup ((fun w : ℝ≥0 => X.X (age + w) ω - X.X age ω) '' Icc 0 v)
    let μ : Measure ℝ := dividendMeasure (fun r (_ : Ω) => M r) ω
    (ENNReal.ofReal (Real.exp (-(q * t))) *
        ENNReal.ofReal (M t.toNNReal - M s.toNNReal) ≤
      ∫⁻ r, if r ∈ Ioc s t then
        ENNReal.ofReal (Real.exp (-(q * r))) else 0 ∂μ) ∧
    ((∫⁻ r, if r ∈ Ioc s t then
        ENNReal.ofReal (Real.exp (-(q * r))) else 0 ∂μ) ≤
      ENNReal.ofReal (Real.exp (-(q * s))) *
        ENNReal.ofReal (M t.toNNReal - M s.toNNReal)) := by sorry
