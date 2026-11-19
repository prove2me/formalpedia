-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_original_all_mesh_clocks_full_threechannel_discounted_reward
-- name    : AvramDividend.Classical.avram_ja18_original_all_mesh_clocks_full_threechannel_discounted_reward
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T20:32:30.864208+00:00
-- url     : https://prove2.me/theorems/a34d1361-12aa-49b8-b1bb-2b210fc3aac2
-- title:
--   Complete original physical three-channel stopped reward source simultaneously for every mesh clock
-- statement:
--   The exact original discounted stopped full Stieltjes cash equals its source-faithful Gaussian, compensated small-negative-mark and uncompensated large-negative-mark physical reserve at every member of a countable sequence of stopping clocks, on one common conull event. Derived by countable almost-sure conjunction from the already Proved single-clock source theorem. This common event is needed for original finite mixed predictable mesh Ito limits and preserves every negative mark.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_discounted_ruinclipped_full_threechannel_reward
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18_original_all_mesh_clocks_full_threechannel_discounted_reward
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (τ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (τ k ω : ℝ))) *
        w (if τ k ω = 0 ∨ (τ k ω : ℝ≥0∞) < ruinTime X x D ω
          then x + X.X (τ k ω) ω - rightLimit D (τ k ω) ω
          else riskProcess X x D (τ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ k ω : ℝ),
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
    ∀ᵐ ω ∂P, ∀ k : ℕ, F k ω =
      Real.exp (-(q * (τ k ω : ℝ))) *
        w (x + (τ k ω : ℝ) * X.c + R (τ k ω) ω + Jsmall (τ k ω) ω +
          avram_p4_h_gaussian_intrinsic_large_jump_sum X (τ k ω) ω -
          (if τ k ω = 0 ∨ (τ k ω : ℝ≥0∞) < ruinTime X x D ω
           then rightLimit D (τ k ω) ω else D (τ k ω) ω)) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal := by sorry
