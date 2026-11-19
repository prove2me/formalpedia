-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_original_spatial_ruinclipped_fullmark_stopped_reward_source
-- name    : AvramDividend.Classical.avram_ja18_original_spatial_ruinclipped_fullmark_stopped_reward_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T21:01:18.114182+00:00
-- url     : https://prove2.me/theorems/5f869099-2da2-4560-a737-1471b47c328b
-- title:
--   Original clipped spatial upcrossing stopped reward exact full Gaussian and negative-mark path source
-- statement:
--   At the exact original spatial sequence of stopping horizons min(ρ, two-sided upper exit at k+1), the full discounted ruin-clipped terminal reward plus full original paymentTimes/ dividendMeasure Stieltjes cash equals the original Lévy drift plus intrinsic Gaussian, compensated small negative marks, and actual uncompensated large negative marks. This is the physical root-specific instantiation of the already Proved all-mesh-clock simultaneous source identity, and identifies the indispensable large-mark source for the Open root physical Ito majorant.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_all_mesh_clocks_full_threechannel_discounted_reward
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18_original_spatial_ruinclipped_fullmark_stopped_reward_source
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ρ : Ω → ℝ≥0)
    (κ : ℕ → Ω → ℝ≥0)
    (hκexact : ∀ k ω, κ k ω =
      (min (ρ ω : ℝ≥0∞)
        (twoSidedExitUpTime X ((k : ℝ) + 1) ω)).toNNReal)
    (H : ℕ → Ω → ℝ)
    (hHsource : ∀ k ω, H k ω =
      Real.exp (-(q * (κ k ω : ℝ))) *
        w (if κ k ω = 0 ∨ (κ k ω : ℝ≥0∞) < ruinTime X x D ω
          then x + X.X (κ k ω) ω - rightLimit D (κ k ω) ω
          else riskProcess X x D (κ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (κ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hJ : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (nhds (Jsmall t ω))) :
    ∀ᵐ ω ∂P, ∀ k : ℕ, H k ω =
      Real.exp (-(q * (κ k ω : ℝ))) *
        w (x + (κ k ω : ℝ) * X.c + R (κ k ω) ω + Jsmall (κ k ω) ω +
          avram_p4_h_gaussian_intrinsic_large_jump_sum X (κ k ω) ω -
          (if κ k ω = 0 ∨ (κ k ω : ℝ≥0∞) < ruinTime X x D ω
           then rightLimit D (κ k ω) ω else D (κ k ω) ω)) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (κ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal := by sorry
