-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_overshooting_liminf_clock_full_expected_cash_budget
-- name    : AvramDividend.Classical.avram_wave7_19_original_overshooting_liminf_clock_full_expected_cash_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:32:27.973463+00:00
-- url     : https://prove2.me/theorems/4674e172-bb5c-47d5-a184-fc2de53f3105
-- title:
--   Original full expected Stieltjes ruin cash from nonmonotone potentially overshooting local clocks
-- statement:
--   For any original source Lévy process and dividend strategy, uniformly bounded discounted paymentTimes cash at measurable clocks τ_n implies the full finite-horizon ruin expected budget if only ruinTime≤liminf_n τ_n almost surely. No monotonicity of τ, no equality of its limit with ruin, no continuity on ruin/overshoot and no UI. Pathwise truncate each τ_n by the actual measurable ruinTime, show min distributes over ENNReal tail infima and suprema even for 0 or ∞ ruin, inherit cash budgets by the original strict paymentTimes inclusion, and use W7-19 generic nonmonotone liminf cash expectation passage. Preserves time-zero right dividend and excludes positive-time ruin-right payment.
-- source:
--   Generic original nonmonotone W7-19 bridge 5b95b760-17b7-4b4a-a03c-5c01a98b69b3 (Proved), source ruinTime_measurable bbfbecf4-7dfc-4812-84f3-8644c2b40b85, paymentTimes_min_mono_horizon 021cfe05-e7e2-40b3-acd0-0850489ea100; exact ENNReal clipped liminf identity verified in accepted source 3103e640-5896-4398-ba8a-3548687e2397.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_original_overshooting_liminf_clock_full_expected_cash_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (τ : ℕ → Ω → ℝ≥0∞)
    (hτmeas : ∀ n : ℕ, Measurable (τ n))
    (hLiminfLower : ∀ᵐ ω ∂P,
      ruinTime X x D ω ≤ (⨆ n : ℕ, ⨅ k : ℕ, τ (n + k) ω))
    (budget : ℝ≥0∞)
    (hBound : ∀ n : ℕ,
      (∫⁻ ω, (∫⁻ t in paymentTimes (τ n ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget := by sorry
