-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_compact_clock_intrinsic_zero_cut_reward_exact
-- name    : AvramDividend.Classical.avram_f6_original_compact_clock_intrinsic_zero_cut_reward_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T08:06:40.413678+00:00
-- url     : https://prove2.me/theorems/e940586e-4cd4-4091-843e-c5d28b85c647
-- title:
--   Original stopped reward in exact intrinsic Gaussian and negative-jump coordinates at zero cutoff
-- statement:
--   At each original ruin-subordinate compact stopping clock σ(k), the physical discounted terminal reward and inclusive Iic dividend cash are exactly the original Lévy drift plus canonical zero-cutoff intrinsic Gaussian residual and negative large-jump sum. This is an exact source identity derived from the proved true-X source and zero-cutoff compensated-mark identity, with unchanged terminal branch and cash.

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

theorem AvramDividend.Classical.avram_f6_original_compact_clock_intrinsic_zero_cut_reward_exact
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
    :
    ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (x + (σ k ω : ℝ) * X.c +
          avram_p4_h_gaussian_intrinsic_large_jump_sum X (σ k ω) ω +
          avram_p4_h_gaussian_intrinsic_truncated_residual X 0 (σ k ω) ω -
          (if σ k ω = 0 ∨ (σ k ω : ℝ≥0∞) < ruinTime X x D ω
           then rightLimit D (σ k ω) ω else D (σ k ω) ω)) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal := by sorry
