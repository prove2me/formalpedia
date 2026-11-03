-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_ae_cofinal_random_clocks_expected_cash_budget
-- name    : AvramDividend.Classical.avram_wave7_19_original_ae_cofinal_random_clocks_expected_cash_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:31:38.948717+00:00
-- url     : https://prove2.me/theorems/f96b1f8a-2579-483d-811c-7cc626d89912
-- title:
--   Original expected full ruin cash budget under almost-sure cofinality of increasing stopped source clocks
-- statement:
--   For the genuine original spectrally negative Levy process and dividend strategy, suppose the W7-18 interior stopped clocks are increasing on each path but exhaust ruinTime only P-almost surely. The exact original paymentTimes cash through T is then bounded P-almost everywhere by the increasing supremum of stopped cash. Measurable stopped Stieltjes rewards with uniform expected ENNReal budgets therefore yield the full expected pre-ruin cash bound by lintegral_mono_ae and lintegral_iSup. This matches the a.s. localisation available for Lévy paths without strengthening the canonical stochastic hypotheses, requiring terminal UI or ignoring time-zero right payments.
-- source:
--   Proved W7-19 source-specific cofinal clock pathwise cash limit f06348b9-331b-447c-b4d3-98e69dd360a5; exact original paymentTimes monotonicity; Mathlib lintegral_mono_ae and lintegral_iSup.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_original_ae_cofinal_random_clocks_expected_cash_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (σ : ℕ → Ω → ℝ≥0∞)
    (hσ : ∀ ω : Ω, Monotone (fun k : ℕ => σ k ω))
    (hSup : ∀ᵐ ω ∂P, (⨆ k : ℕ, σ k ω) = ruinTime X x D ω)
    (hMeas : ∀ k : ℕ, Measurable (fun ω : Ω =>
      ∫⁻ t in paymentTimes (σ k ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)))
    (budget : ℝ≥0∞)
    (hBound : ∀ k : ℕ,
      (∫⁻ ω, (∫⁻ t in paymentTimes (σ k ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget := by sorry
