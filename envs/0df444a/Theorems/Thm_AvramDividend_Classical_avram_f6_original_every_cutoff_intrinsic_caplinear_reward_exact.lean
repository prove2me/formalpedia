-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_every_cutoff_intrinsic_caplinear_reward_exact
-- name    : AvramDividend.Classical.avram_f6_original_every_cutoff_intrinsic_caplinear_reward_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T10:00:30.20909+00:00
-- url     : https://prove2.me/theorems/88a19168-d757-4124-92f9-3f4015d5a871
-- title:
--   True original compact-clock payoff in physical caplinear Gaussian and negative marked-jump intrinsic cutoff coordinates
-- statement:
--   At every true original ruin-subordinate compact clock, for every intrinsic Gaussian/small-negative-mark cutoff, the exact discounted terminal reward and inclusive right-dividend cash equal the canonical caplinear continuation V of the actual Lévy drift X.c, compensated intrinsic small band, negative large-jump sum and Gaussian residual, with original terminal ruin versus rightLimit D branch preserved. The proof combines already Proved public same-X physical residual decomposition and original true terminal caplinear cash identity. No abstract martingale or above-cap regularity.

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

theorem AvramDividend.Classical.avram_f6_original_every_cutoff_intrinsic_caplinear_reward_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
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
        (let V : ℝ → ℝ := fun z =>
           if ENNReal.ofReal z ≤ C then w z
           else w C.toReal + (z - C.toReal)
         V (x + (σ k ω : ℝ) * X.c +
          avram_p4_h_gaussian_intrinsic_small_band_compensated X cut (σ k ω) ω +
          avram_p4_h_gaussian_intrinsic_large_jump_sum X (σ k ω) ω +
          avram_p4_h_gaussian_intrinsic_truncated_residual X cut (σ k ω) ω -
          (if σ k ω = 0 ∨ (σ k ω : ℝ≥0∞) < ruinTime X x D ω
           then rightLimit D (σ k ω) ω else D (σ k ω) ω))) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal := by sorry
