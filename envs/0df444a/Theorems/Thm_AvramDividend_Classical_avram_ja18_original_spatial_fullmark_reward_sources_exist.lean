-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_original_spatial_fullmark_reward_sources_exist
-- name    : AvramDividend.Classical.avram_ja18_original_spatial_fullmark_reward_sources_exist
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T21:01:48.519205+00:00
-- url     : https://prove2.me/theorems/28d3b642-d303-4045-b18f-649ba9950ffd
-- title:
--   Original spatial upcrossing fullmark stopped cash source exists from Standing finite activity
-- statement:
--   Directly from original spectrally negative finite negative activity Standing source assumptions, construct physical intrinsic Gaussian R and compensated smallnegative Jsmall with their genuine source limits, Gaussian pointwise integrability, initial martingale property, and exact original spatially-clipped upcrossing discounted stopped terminal reward plus full Stieltjes cash represented at every spatial cutoff as physical drift + R + Jsmall + actual uncompensated large-negative marks. This removes arbitrary source hypotheses from the blocked original spatial two-noise ledger.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_all_mesh_clocks_full_threechannel_discounted_reward
import Theorems.Thm_AvramDividend_Classical_avram_b212_original_finite_activity_global_intrinsic_gaussian_smallmark_martingale_sources
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18_original_spatial_fullmark_reward_sources_exist
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
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
    :
    ∃ (R Jsmall : ℝ≥0 → Ω → ℝ),
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun j : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X j t ω)
          atTop (nhds (R t ω))) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun j : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X j t ω)
          atTop (nhds (Jsmall t ω))) ∧
      (∀ t : ℝ≥0, Integrable (R t) P) ∧
      (∀ a b : ℝ≥0, a ≤ b →
        ∀ᵐ ω ∂P, condExp (𝓕.rightCont a) P (R b) ω = R a ω) ∧
    ∀ᵐ ω ∂P, ∀ k : ℕ, H k ω =
      Real.exp (-(q * (κ k ω : ℝ))) *
        w (x + (κ k ω : ℝ) * X.c + R (κ k ω) ω + Jsmall (κ k ω) ω +
          avram_p4_h_gaussian_intrinsic_large_jump_sum X (κ k ω) ω -
          (if κ k ω = 0 ∨ (κ k ω : ℝ≥0∞) < ruinTime X x D ω
           then rightLimit D (κ k ω) ω else D (κ k ω) ω)) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (κ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal := by sorry
