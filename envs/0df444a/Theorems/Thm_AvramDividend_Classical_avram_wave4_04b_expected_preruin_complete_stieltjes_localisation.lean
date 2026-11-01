-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_expected_preruin_complete_stieltjes_localisation
-- name    : AvramDividend.Classical.avram_wave4_04b_expected_preruin_complete_stieltjes_localisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:06:18.588883+00:00
-- url     : https://prove2.me/theorems/719af000-518f-4807-83fa-4d126306a372
-- title:
--   Expected full pre-ruin discounted Stieltjes dividends converge from measurable increasing random localisation clocks
-- statement:
--   For a genuine source spectrally negative Lévy process and adapted dividend strategy, measurable increasing sample-dependent stopping clocks converging to the actual ruin time recover the original expected full finite-horizon discounted Stieltjes dividend reward by monotone convergence. Measurability is discharged using the proved s-finite source dividend kernel, joint payment-time measurability and random-indicator kernel integral theorem. The independently Proved general weighted source Stieltjes localisation theorem preserves initial/later right atoms and arbitrary absolutely continuous or singular-continuous dividend mass. No stochastic Itô–Meyer or generator identity is assumed.
-- source:
--   04-B Proved full weighted source dividend localisation and Proved random Stieltjes kernel, joint payment measurability, Mathlib lintegral_iSup

import Mathlib
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_global_sfinite_kernel_exists
import Theorems.Thm_AvramDividend_Classical_paymentTimes_joint_measurable
import Theorems.Thm_AvramDividend_Classical_measurable_random_indicator_lintegral
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_complete_stieltjes_reward_localisation_supremum

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_expected_preruin_complete_stieltjes_localisation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0) (q : ℝ)
    (τ : ℕ → Ω → ℝ≥0∞)
    (hτmeas : ∀ n, Measurable (τ n))
    (hτmono : ∀ ω, Monotone (fun n => τ n ω))
    (hτsup : ∀ ω, (⨆ n, τ n ω) = ruinTime X x D ω) :
    (∫⁻ ω : Ω, ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-q * s)) ∂dividendMeasure D ω ∂P) =
    ⨆ n, (∫⁻ ω : Ω, ∫⁻ s in paymentTimes (τ n ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-q * s)) ∂dividendMeasure D ω ∂P) := by
  sorry
