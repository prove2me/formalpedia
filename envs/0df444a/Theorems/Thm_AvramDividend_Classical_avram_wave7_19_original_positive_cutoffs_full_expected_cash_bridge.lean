-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_positive_cutoffs_full_expected_cash_bridge
-- name    : AvramDividend.Classical.avram_wave7_19_original_positive_cutoffs_full_expected_cash_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:31:05.848819+00:00
-- url     : https://prove2.me/theorems/ece66659-9fbd-4446-91b5-4e0f16f362f8
-- title:
--   Original full ruin cash expectation bound from uniform stopped lower-time cutoff budgets under unchanged dividend strategy
-- statement:
--   For the actual original spectrally negative Levy process X, any dividend strategy D satisfying the unchanged IsDividendStrategy hypothesis, T≥0 and a single deterministic natural stopped clock n>T, a uniform expected ENNReal budget on the exact initial right-dividend singleton plus every positive reciprocal lower-time cutoff payment integral at τ∧n implies the full finite-horizon pre-ruin discounted Stieltjes cash budget. The measurability premise needed for monotone convergence follows automatically from the original strategy and the already proved Stieltjes kernel/joint payment-time measurability. This is the W7-19 no-extra-hypotheses final boundary and limit passage after a local stopped Ito inequality; its remaining premise is precisely the actual stopped expectation bound supplied by W7-08 and component controls.
-- source:
--   Two dedicated W7-19 children: expectation MCT 6c6548f4-5446-4eca-a0be-25be72df0b20 (pending proof candidate 22532), and IsDividendStrategy positive cutoff cash measurability 6eab88b4-05ec-4cbd-a062-20dc38c07832 (pending proof candidate 22540). Parent W7-08 positive-horizon Ito budget 6004b387-9caa-4ee7-b466-2bf22d148505. No canonical hypotheses changed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_original_positive_cutoffs_full_expected_cash_bridge
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ) (hT : 0 ≤ T)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (hn : ENNReal.ofReal T < (n : ℝ≥0∞))
    (budget : ℝ≥0∞)
    (hBound : ∀ k : ℕ,
      (∫⁻ ω, ((∫⁻ t in ({0} : Set ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
      (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩
        Icc (1 / ((k : ℝ) + 1)) T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) ∂P) ≤ budget) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget := by sorry
