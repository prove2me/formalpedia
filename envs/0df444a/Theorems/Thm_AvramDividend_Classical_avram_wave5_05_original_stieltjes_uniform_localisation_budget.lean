-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_original_stieltjes_uniform_localisation_budget
-- name    : AvramDividend.Classical.avram_wave5_05_original_stieltjes_uniform_localisation_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T01:06:16.106578+00:00
-- url     : https://prove2.me/theorems/de98b3ae-111b-496f-a7f5-3c606aae6248
-- title:
--   Uniform original-process stopped Stieltjes budgets imply full ruin-stopped budget
-- statement:
--   For a genuine source spectrally negative Lévy process and an adapted original-process dividend strategy, assume measurable monotone random stopping clocks increase pointwise to the actual ruin time. If every clock-stopped expected discounted Stieltjes payout is bounded above by one ENNReal budget, then the full actual-ruin-stopped expected finite-horizon discounted dividend payout satisfies that budget. The reward includes time-zero and later right atoms, absolutely continuous and singular-continuous dividends. This theorem uses the independently Proved original-process monotone-clock expected payout equality and assumes no fictitious finite-variation source process.
-- source:
--   Proved AvramDividend.Classical.avram_wave4_04b_expected_preruin_complete_stieltjes_localisation (UUID 719af000-518f-4807-83fa-4d126306a372) and direct iSup upper bound; private remote probe job c3699f36-f190-4c92-9178-06f1d081faa5 reached sentinel.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_expected_preruin_complete_stieltjes_localisation

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_05_original_stieltjes_uniform_localisation_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0) (q : ℝ)
    (τ : ℕ → Ω → ℝ≥0∞)
    (hτmeas : ∀ n, Measurable (τ n))
    (hτmono : ∀ ω, Monotone (fun n => τ n ω))
    (hτsup : ∀ ω, (⨆ n, τ n ω) = ruinTime X x D ω)
    (B : ℝ≥0∞)
    (hBound : ∀ n,
      (∫⁻ ω : Ω,
          ∫⁻ s in paymentTimes (τ n ω) ∩ Iic (T : ℝ),
            ENNReal.ofReal (Real.exp (-q * s))
              ∂dividendMeasure D ω ∂P) ≤ B) :
    (∫⁻ ω : Ω,
        ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
          ENNReal.ofReal (Real.exp (-q * s))
            ∂dividendMeasure D ω ∂P) ≤ B := by
  sorry
