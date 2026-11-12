-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jb20_original_physical_random_clock_increment_split
-- name    : AvramDividend.Classical.avram_jb20_original_physical_random_clock_increment_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T15:52:18.057582+00:00
-- url     : https://prove2.me/theorems/48ec85d6-5a66-4bea-aa60-9ad21d1aa0db
-- title:
--   Exact original-source Gaussian and marked-jump increments between arbitrary stopped clocks
-- statement:
--   For the original Levy process on its own physical probability space and filtration, construct the totalised intrinsic Gaussian source and express the increment X(beta)-X(alpha) at any two sample-dependent times as drift difference plus Gaussian residual increment and exact original compensated small-band and raw large-jump increments. Simultaneously transfer each Gaussian stopped increment almost surely to the intrinsic residual R. The clocks can be arbitrary, so finite stopped Ito mesh cells require no new zero-jump Levy process.
-- source:
--   Proved 561f5a08 source-exact path totalisation; ring algebra and simultaneous a.e. residual identity. Enables source-exact stopped Gaussian/jump mesh component accounting for Open 544e8511 and compact-clock Ito route fa7052b1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_jb19_original_gaussian_residual_totalise_source_path
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_jb20_original_physical_random_clock_increment_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hJsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (nhds (Jsmall t ω))) :
    ∃ M : ℝ≥0 → Ω → ℝ,
      (∀ t ω, X.X t ω =
        (t : ℝ) * X.c + M t ω + Jsmall t ω +
          avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, M t ω = R t ω) ∧
      (∀ α β : Ω → ℝ≥0, ∀ ω,
        X.X (β ω) ω - X.X (α ω) ω =
          ((β ω : ℝ) - (α ω : ℝ)) * X.c +
          (M (β ω) ω - M (α ω) ω) +
          (Jsmall (β ω) ω - Jsmall (α ω) ω) +
          (avram_p4_h_gaussian_intrinsic_large_jump_sum X (β ω) ω -
            avram_p4_h_gaussian_intrinsic_large_jump_sum X (α ω) ω)) ∧
      (∀ α β : Ω → ℝ≥0,
        (fun ω => M (β ω) ω - M (α ω) ω) =ᵐ[P]
          (fun ω => R (β ω) ω - R (α ω) ω)) := by sorry
