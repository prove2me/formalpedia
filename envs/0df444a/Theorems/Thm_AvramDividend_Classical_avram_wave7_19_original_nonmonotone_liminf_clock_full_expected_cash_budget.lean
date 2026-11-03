-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_nonmonotone_liminf_clock_full_expected_cash_budget
-- name    : AvramDividend.Classical.avram_wave7_19_original_nonmonotone_liminf_clock_full_expected_cash_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:26:13.245227+00:00
-- url     : https://prove2.me/theorems/5b95b760-17b7-4b4a-a03c-5c01a98b69b3
-- title:
--   Original finite-horizon expected Stieltjes ruin cash under nonmonotone a.s. liminf-cofinal random clocks
-- statement:
--   No reserve process continuity, artificial state-boundary hypotheses or monotone clock assumption. For a measurable original Lévy/dividend source clock sequence τ whose P-a.s. liminf equals the actual ruinTime, its tail infimum σ_n = inf_k τ_(n+k) is measurable, increases in n and exhausts ruin almost surely. Exact paymentTimes Stieltjes cash at σ_n is bounded by cash at τ_n, preserving time-zero right-dividend atom. The accepted W7-19 a.s.-cofinal monotone source cash expectation bridge then yields the full finite-horizon budget from uniformly bounded nonmonotone stopped budgets. All assumptions are already mathematical localisation facts to be supplied by W7-18, independent of UBV canonical smoothness and sign hypotheses.
-- source:
--   Proved original a.s.-cofinal W7-19 cash bridge f96b1f8a-2579-483d-811c-7cc626d89912 and random-clock measurability f2bd15ce-a7f8-404d-a706-f94293b9fda3; source-faithful tail-infimum construction from accepted b7105a08-8cdc-4cb9-a67c-5eff0eb612fd, with canonical stochastic hypotheses entirely unused.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_original_nonmonotone_liminf_clock_full_expected_cash_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (τ : ℕ → Ω → ℝ≥0∞)
    (hτmeas : ∀ n : ℕ, Measurable (τ n))
    (hLiminf : ∀ᵐ ω ∂P,
      (⨆ n : ℕ, ⨅ k : ℕ, τ (n + k) ω) = ruinTime X x D ω)
    (budget : ℝ≥0∞)
    (hBound : ∀ n : ℕ,
      (∫⁻ ω, (∫⁻ t in paymentTimes (τ n ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget := by sorry
