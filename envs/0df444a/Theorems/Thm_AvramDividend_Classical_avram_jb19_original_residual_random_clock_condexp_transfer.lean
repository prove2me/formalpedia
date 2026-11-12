-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jb19_original_residual_random_clock_condexp_transfer
-- name    : AvramDividend.Classical.avram_jb19_original_residual_random_clock_condexp_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T13:45:30.304057+00:00
-- url     : https://prove2.me/theorems/05b97f01-2923-48ad-bf5b-a512884fad22
-- title:
--   Original Gaussian residual totalisation respects every random clock, stopped integrability and initial conditional expectation
-- statement:
--   From original simultaneous almost-sure Gaussian and compensated-jump source limits, construct an exact all-path Lévy source Gaussian field M. Its values agree with the intrinsic Gaussian residual R not only at every deterministic time but also at any random nonnegative clock, without imposing spurious measurability on the clock. Integrability of the stopped R transfers to stopped M, and their conditional expectations on the original right-continuous initial sigma algebra are equal almost everywhere. This is a bridge needed to transport any independently established Gaussian optional-stopping/centering certificate to original physical Ito accounting.
-- source:
--   Proved 561f5a08 source totalisation, Mathlib integrability congruence and condExp_congr_ae. Supports finite-mixed 544e8511 and localised source fa7052b1 once stopped R martingale certificates are available.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_jb19_original_gaussian_residual_totalise_source_path
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_jb19_original_residual_random_clock_condexp_transfer
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
      (∀ σ : Ω → ℝ≥0,
        (fun ω => M (σ ω) ω) =ᵐ[P] (fun ω => R (σ ω) ω) ∧
        (Integrable (fun ω => R (σ ω) ω) P →
          Integrable (fun ω => M (σ ω) ω) P) ∧
        condExp (𝓕.rightCont 0) P (fun ω => M (σ ω) ω) =ᵐ[P]
          condExp (𝓕.rightCont 0) P (fun ω => R (σ ω) ω)) := by sorry
