-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_original_ruinclipped_reserve_two_physical_noises_fullmark
-- name    : AvramDividend.Classical.avram_ja18_original_ruinclipped_reserve_two_physical_noises_fullmark
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T17:52:34.095931+00:00
-- url     : https://prove2.me/theorems/22f3eeae-24e8-436d-b0e2-04dbc9cd620c
-- title:
--   Original stopped two physical martingale sources including full compensated negative-jump marks
-- statement:
--   For the original spectrally negative finite-negative-activity Levy source with its intrinsic Gaussian residual R, the genuine full compensated negative-mark martingale is Jfull=X(t)-E[X(1)]t-R(t), which equals original Jsmall+actual large-negative-jump sum+(c-E[X1])t. The actual stopped pre-/postruin reserve at every bounded stopping time is exactly initial capital plus mean drift plus intrinsic Gaussian noise plus this full jump martingale, less the original correct dividend right-limit/ruin-contact payment. The stopped full jump martingale is integrable and has right-continuous initial conditional expectation zero. This is a genuine physical two-noise corrected replacement for the incomplete Jsmall-only B219 source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_intrinsic_gaussian_smallmark_largemark_full_path_ae_split
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_stopped_W_sameX_intrinsic_residual
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_cutoff
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin15_original_compensated_jump_stopped_martingale_public
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18_original_ruinclipped_reserve_two_physical_noises_fullmark
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (W : Ω → ℝ)
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
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω) :
    let μ : ℝ := ∫ ω, X.X 1 ω ∂P
    ∃ Jfull : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Jfull t ω =
          Jsmall t ω +
          avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω +
          (t : ℝ) * (X.c - μ)) ∧
      (∀ᵐ ω ∂P,
        W ω = x + (τ ω : ℝ) * μ + R (τ ω) ω + Jfull (τ ω) ω -
          (if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
           then rightLimit D (τ ω) ω else D (τ ω) ω)) ∧
      Integrable (fun ω => Jfull (τ ω) ω) P ∧
      (∀ᵐ ω ∂P,
        condExp (𝓕.rightCont 0) P
          (fun ω => Jfull (τ ω) ω) ω = 0) := by sorry
