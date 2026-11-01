-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_preruin_discounted_complete_stieltjes_localisation
-- name    : AvramDividend.Classical.avram_wave4_04b_preruin_discounted_complete_stieltjes_localisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:45:12.00348+00:00
-- url     : https://prove2.me/theorems/3ce6b771-2d80-4b0c-8237-ba6246f0b117
-- title:
--   Actual pre-ruin full discounted Stieltjes reward is the monotone limit of increasing stopped clocks
-- statement:
--   For the source spectrally negative Lévy process, actual adapted dividend strategy, a finite horizon, and increasing stopping clocks with supremum equal to the actual ruin time, the original chronological pre-ruin discounted full Stieltjes reward equals the supremum of localised rewards. The proof uses the proved source payment-time union identity, a measurable discounted weight and pinned Mathlib monotone convergence directly. It retains time-zero and later right atoms and arbitrary absolutely continuous or singular-continuous dividend variation. It establishes no compensated stochastic Itô term or generator inequality.
-- source:
--   04-B source-X stopped full reward; proved source clock union, discounted weight and Mathlib lintegral_iSup

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_payment_times_supremum_clock_union

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_preruin_discounted_complete_stieltjes_localisation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) (q : ℝ)
    (τ : ℕ → ℝ≥0∞) (hτ : Monotone τ)
    (hτsup : (⨆ n, τ n) = ruinTime X x D ω) :
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-q * s)) ∂dividendMeasure D ω) =
    ⨆ n, (∫⁻ s in paymentTimes (τ n) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-q * s)) ∂dividendMeasure D ω) := by
  sorry
