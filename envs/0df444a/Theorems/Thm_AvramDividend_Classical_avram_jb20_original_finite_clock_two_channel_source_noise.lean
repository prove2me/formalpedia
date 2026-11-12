-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jb20_original_finite_clock_two_channel_source_noise
-- name    : AvramDividend.Classical.avram_jb20_original_finite_clock_two_channel_source_noise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T16:28:43.5731+00:00
-- url     : https://prove2.me/theorems/59aa4e07-41d1-41c2-be1a-c911a0f7761f
-- title:
--   Finite-range original physical clock has integrable initially centred Gaussian and jump channels
-- statement:
--   At a finite-range bounded true stopping clock, the original mixed process decomposes into deterministic Levy drift, separately integrable and initially centred Gaussian and small compensated-jump sources, and the raw large-negative-jump source; no replacement probability space and no truncation of ruin or payment atoms.
-- source:
--   Depends on Proved physical source 48ec85d6 and pending new finite-range optional-sampling lemma; directly supports finite-clock noise stage of 544e8511.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_jb20_original_physical_random_clock_increment_split
import Theorems.Thm_AvramDividend_Classical_avram_jb20_original_gaussian_finite_range_stop_condexp
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_jb20_original_finite_clock_two_channel_source_noise
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
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
        atTop (nhds (Jsmall t ω)))
    (hRint : ∀ t : ℝ≥0, Integrable (R t) P)
    (hRmart : ∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P,
        condExp (𝓕.rightCont s) P (R t) ω = R s ω)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hτbound : ∀ ω, τ ω ≤ T)
    (S : Finset ℝ≥0) (hτrange : ∀ ω, τ ω ∈ S)
    (hJI : Integrable (fun ω => Jsmall (τ ω) ω) P)
    (hJcenter : ∀ᵐ ω ∂P,
      condExp (𝓕.rightCont 0) P
        (fun ω => Jsmall (τ ω) ω) ω = 0) :
    ∃ MG MJ : Ω → ℝ,
      Integrable MG P ∧ Integrable MJ P ∧
      (∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P MG ω = 0) ∧
      (∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P MJ ω = 0) ∧
      (∀ᵐ ω ∂P,
        X.X (τ ω) ω =
          (τ ω : ℝ) * X.c + MG ω + MJ ω +
            avram_p4_h_gaussian_intrinsic_large_jump_sum X (τ ω) ω) := by sorry
