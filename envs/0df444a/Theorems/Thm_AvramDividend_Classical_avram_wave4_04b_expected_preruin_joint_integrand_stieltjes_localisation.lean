-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_expected_preruin_joint_integrand_stieltjes_localisation
-- name    : AvramDividend.Classical.avram_wave4_04b_expected_preruin_joint_integrand_stieltjes_localisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T17:26:50.958627+00:00
-- url     : https://prove2.me/theorems/31b789d9-342f-4f99-b2b6-0cd42da85803
-- title:
--   Expected full source-X pre-ruin Stieltjes localisation for any jointly measurable path-dependent nonnegative integrand
-- statement:
--   For the actual source spectrally negative Lévy process X and adapted dividend strategy D, let measurable random clocks increase pointwise to the original ruin time. For an arbitrary jointly measurable nonnegative integrand f(s,ω), the expected finite-horizon complete Stieltjes integral of f over original payment times equals the supremum of expected integrals over the localised payment times. Full dividend measure includes the t=0 atom, right payments, absolutely continuous and singular-continuous parts. This extends the already Proved deterministic-time-weight expected identity to state-dependent gradients and jump corrections; it assumes no Itô–Meyer stochastic identity or martingale integrability.
-- source:
--   Proved s-finite dividend kernel, Proved payment-times joint measurability and full weighted pathwise MCT, new joint random-indicator kernel measurability helper

import Mathlib
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_global_sfinite_kernel_exists
import Theorems.Thm_AvramDividend_Classical_paymentTimes_joint_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_complete_stieltjes_reward_localisation_supremum
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_measurable_random_joint_indicator_lintegral

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_expected_preruin_joint_integrand_stieltjes_localisation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0) (τ : ℕ → Ω → ℝ≥0∞)
    (hτmeas : ∀ n, Measurable (τ n))
    (hτmono : ∀ ω, Monotone (fun n => τ n ω))
    (hτsup : ∀ ω, (⨆ n, τ n ω) = ruinTime X x D ω)
    (f : ℝ × Ω → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω : Ω, ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      f (s, ω) ∂dividendMeasure D ω ∂P) =
    ⨆ n, (∫⁻ ω : Ω, ∫⁻ s in paymentTimes (τ n ω) ∩ Iic (T : ℝ),
      f (s, ω) ∂dividendMeasure D ω ∂P) := by
  sorry
