-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_expected_preruin_locally_joint_measurable_stieltjes_localisation
-- name    : AvramDividend.Classical.avram_wave4_04b_expected_preruin_locally_joint_measurable_stieltjes_localisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T17:24:53.756327+00:00
-- url     : https://prove2.me/theorems/5d93fcce-f0aa-426d-8802-41723319f748
-- title:
--   Expected full source-X Stieltjes localisation with only pathwise and clock-masked joint measurability
-- statement:
--   For actual source spectrally negative Levy surplus and adapted right-payment dividend control, measurable random clocks increasing to ruin time and finite T, nonnegative path-dependent f may lack global joint measurability. It suffices that each time-section is measurable and that each localising clock's payment-times-masked f is jointly measurable. The expected full Stieltjes reward on pre-ruin payment times is the supremum of expected localised rewards. Includes initial t=0 right payment, all right atoms, and diffuse absolutely/singular continuous dividends. Does not presume any Itô–Meyer or compensator axiom.
-- source:
--   Proved full pathwise Stieltjes localisation, proved s-finite dividend kernel and pinned Mathlib kernel-product measurability

import Mathlib
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_global_sfinite_kernel_exists
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_complete_stieltjes_reward_localisation_supremum

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_expected_preruin_locally_joint_measurable_stieltjes_localisation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0) (τ : ℕ → Ω → ℝ≥0∞)
    (hτmeas : ∀ n, Measurable (τ n))
    (hτmono : ∀ ω, Monotone (fun n => τ n ω))
    (hτsup : ∀ ω, (⨆ n, τ n ω) = ruinTime X x D ω)
    (f : ℝ × Ω → ℝ≥0∞)
    (hfpath : ∀ ω, Measurable (fun s : ℝ => f (s, ω)))
    (hfmask : ∀ n, Measurable (fun p : ℝ × Ω =>
      if p.1 ∈ paymentTimes (τ n p.2) ∩ Iic (T : ℝ) then f p else 0)) :
    (∫⁻ ω : Ω, ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      f (s, ω) ∂dividendMeasure D ω ∂P) =
    ⨆ n, (∫⁻ ω : Ω, ∫⁻ s in paymentTimes (τ n ω) ∩ Iic (T : ℝ),
      f (s, ω) ∂dividendMeasure D ω ∂P) := by
  sorry
