-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_original_ruinclipped_discounted_full_cash_reward_threechannel
-- name    : AvramDividend.Classical.avram_ja18_original_ruinclipped_discounted_full_cash_reward_threechannel
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T17:47:22.789321+00:00
-- url     : https://prove2.me/theorems/e8bb2d0c-1dbf-4859-8e19-dda0be6d69c4
-- title:
--   Exact ruinclipped discounted full Stieltjes cash reward on physical Gaussian, small and large negative marks
-- statement:
--   For the original spectrally negative Levy driver and its actual dividend measure, the exact discounted stopped terminal reward plus full closed payment-set Stieltjes cash equals the same reward evaluated on the physical drift, Gaussian residual limit, compensated small negative jumps and the indispensable actual uncompensated large-negative-mark process, with the true pre-ruin/post-ruin dividend branch. This is an original-source reward-level bridge for repairing the blocked B219 two-noise cash Ito ledger.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_ruinclipped_stopped_reserve_full_threechannel_source
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18_original_ruinclipped_discounted_full_cash_reward_threechannel
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ)
    (D : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0)
    (F : Ω → ℝ)
    (hF : ∀ ω, F ω =
      Real.exp (-(q * (τ ω : ℝ))) *
        w (if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
          then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
          else riskProcess X x D (τ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hJ : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (nhds (Jsmall t ω))) :
    ∀ᵐ ω ∂P, F ω =
      Real.exp (-(q * (τ ω : ℝ))) *
        w (x + (τ ω : ℝ) * X.c + R (τ ω) ω + Jsmall (τ ω) ω +
          avram_p4_h_gaussian_intrinsic_large_jump_sum X (τ ω) ω -
          (if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
           then rightLimit D (τ ω) ω else D (τ ω) ω)) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal := by sorry
