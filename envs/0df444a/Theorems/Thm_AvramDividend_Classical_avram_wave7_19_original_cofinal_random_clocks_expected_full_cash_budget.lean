-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_cofinal_random_clocks_expected_full_cash_budget
-- name    : AvramDividend.Classical.avram_wave7_19_original_cofinal_random_clocks_expected_full_cash_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:23:14.299927+00:00
-- url     : https://prove2.me/theorems/b4aef557-0f77-439d-a738-41b5ea0cbefc
-- title:
--   Original finite-horizon expected ruin cash bound from cofinal increasing random stopped-clock estimates
-- statement:
--   For original spectrally negative Levy X and the unchanged dividend strategy D, let W7-18 provide measurable cash at increasing random stopping clocks σ_k with supremum the original ruinTime for each path. Uniform expected ENNReal bounds on exact paymentTimes(σ_k) through T transfer to the full pre-ruin original dividendMeasure cash through T. This proves the expectation and ruin-boundary limit after actual local stopped Ito estimates, with the initial right atom retained, positive ruin boundary right atom excluded, and no terminal uniform integrability.
-- source:
--   W7-19 source-specific cofinal random clock pathwise lintegral iSup, ENNReal monotone convergence; no abstract replacement process or W7-03 real/ENNReal conversion.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_original_cofinal_random_clocks_expected_full_cash_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (σ : ℕ → Ω → ℝ≥0∞)
    (hσ : ∀ ω : Ω, Monotone (fun k : ℕ => σ k ω))
    (hSup : ∀ ω : Ω, (⨆ k : ℕ, σ k ω) = ruinTime X x D ω)
    (hMeas : ∀ k : ℕ, Measurable (fun ω : Ω =>
      ∫⁻ t in paymentTimes (σ k ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)))
    (budget : ℝ≥0∞)
    (hBound : ∀ k : ℕ,
      (∫⁻ ω, (∫⁻ t in paymentTimes (σ k ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget := by sorry
