-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_compact_clock_every_cutoff_reward_exact
-- name    : AvramDividend.Classical.avram_f6_original_compact_clock_every_cutoff_reward_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T08:25:14.37412+00:00
-- url     : https://prove2.me/theorems/f14016e1-f1d7-444c-9d20-ef49b8c2df92
-- title:
--   Original compact stopped payoff and inclusive dividend cash in every physical Gaussian and jump cutoff
-- statement:
--   For every intrinsic cutoff and original subordinate clock σ(k), exactly identify the stopped reward with original drift, finite-cutoff intrinsic Gaussian residual, compensated negative small-mark sum and negative large-jump sum. Keep exact terminal at ruin and inclusive Iic dividend cash. Use the public original same-X decomposition only.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_compact_clock_every_cutoff_reward_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (cut : ℕ) :
    ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (x + (σ k ω : ℝ) * X.c +
          avram_p4_h_gaussian_intrinsic_small_band_compensated X cut (σ k ω) ω +
          avram_p4_h_gaussian_intrinsic_large_jump_sum X (σ k ω) ω +
          avram_p4_h_gaussian_intrinsic_truncated_residual X cut (σ k ω) ω -
          (if σ k ω = 0 ∨ (σ k ω : ℝ≥0∞) < ruinTime X x D ω
           then rightLimit D (σ k ω) ω else D (σ k ω) ω)) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal := by sorry
