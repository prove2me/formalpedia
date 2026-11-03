-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_clipped_clock_lower_cutoff_expectation_budget_mct
-- name    : AvramDividend.Classical.avram_wave7_19_original_clipped_clock_lower_cutoff_expectation_budget_mct
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:21:33.038899+00:00
-- url     : https://prove2.me/theorems/6c6548f4-5446-4eca-a0be-25be72df0b20
-- title:
--   Original finite-horizon full Stieltjes expectation bound from clipped-clock zero-atom and positive lower-cutoff stopped budgets
-- statement:
--   Fix the original spectrally negative Levy process, dividend strategy, finite horizon T and natural clock n satisfying n>T. If the exact original pathwise zero-right-dividend atom plus each positive reciprocal lower-cutoff clipped-clock Stieltjes payoff is measurable and its expected ENNReal value is bounded uniformly by a budget, then the full original finite-horizon discounted ruin cash has expected ENNReal value at most that budget. The source-specific pathwise identity and monotone convergence supply the limit. The measurability and local budget premises are the genuine component obligations, not additional canonical UBV hypotheses; no terminal uniform integrability, atomlessness, reserve continuity or global localisation limit is assumed.
-- source:
--   Accepted W7-19 pathwise clipped-clock cash identity e37ed2bb-b657-49bd-93f6-f63db13851c9 (candidate 22520), source original zero atom, pinned Mathlib ENNReal.add_iSup and MeasureTheory.lintegral_mono_set, W7-08 interior Ito core 6004b387-9caa-4ee7-b466-2bf22d148505

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_clipped_clock_zero_atom_lower_cutoff_lintegral_iSup
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_original_clipped_clock_lower_cutoff_expectation_budget_mct
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ) (hT : 0 ≤ T)
    (D : ℝ≥0 → Ω → ℝ) (n : ℕ)
    (hn : ENNReal.ofReal T < (n : ℝ≥0∞)) (budget : ℝ≥0∞)
    (hMeas : ∀ k : ℕ, Measurable (fun ω : Ω =>
      (∫⁻ t in ({0} : Set ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
      (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩
        Icc (1 / ((k : ℝ) + 1)) T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))))
    (hBound : ∀ k : ℕ,
      (∫⁻ ω, ((∫⁻ t in ({0} : Set ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
      (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩
        Icc (1 / ((k : ℝ) + 1)) T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) ∂P) ≤ budget) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget := by sorry
