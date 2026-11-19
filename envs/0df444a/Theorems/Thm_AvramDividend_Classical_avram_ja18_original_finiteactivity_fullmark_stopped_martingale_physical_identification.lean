-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_original_finiteactivity_fullmark_stopped_martingale_physical_identification
-- name    : AvramDividend.Classical.avram_ja18_original_finiteactivity_fullmark_stopped_martingale_physical_identification
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T17:48:32.273141+00:00
-- url     : https://prove2.me/theorems/15f150ef-6f39-421f-8c64-160e9771db9e
-- title:
--   Original physical full negative-mark stopped martingale: small, large and compensating drift channels
-- statement:
--   For the genuine original finite-activity Levy source, identify the canonical full jump martingale Jfull(t)=X(t)-t E[X(1)]-R(t) with the physical compensated small-negative-mark process, the uncompensated large-negative-mark process and the exact deterministic compensation t(c-E[X(1)]). The same Jfull has integrable bounded stopping-time value and initial conditional expectation zero, directly by the already Proved original stopped compensated-jump martingale. This delivers the missing physically correct second noise for finite mixed Gaussian/jump stopped Ito cash.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_intrinsic_gaussian_smallmark_largemark_full_path_ae_split
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin15_original_compensated_jump_stopped_martingale_public
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18_original_finiteactivity_fullmark_stopped_martingale_physical_identification
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hJ : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (nhds (Jsmall t ω)))
    (hRint : ∀ t : ℝ≥0, Integrable (R t) P)
    (hRmart : ∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P, condExp (𝓕.rightCont s) P (R t) ω = R s ω)
    (n : ℕ) (hn : 0 < n)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0)) :
    let μ : ℝ := ∫ ω, X.X 1 ω ∂P
    ∃ Jfull : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Jfull t ω =
          Jsmall t ω +
            avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω +
            (t : ℝ) * (X.c - μ)) ∧
      (∀ t : ℝ≥0, Integrable (Jfull t) P) ∧
      (∀ s t : ℝ≥0, s ≤ t →
        ∀ᵐ ω ∂P,
          condExp (𝓕.rightCont s) P (Jfull t) ω = Jfull s ω) ∧
      Integrable (fun ω => Jfull (τ ω) ω) P ∧
      (∀ᵐ ω ∂P,
        condExp (𝓕.rightCont 0) P
          (fun ω => Jfull (τ ω) ω) ω = 0) := by sorry
