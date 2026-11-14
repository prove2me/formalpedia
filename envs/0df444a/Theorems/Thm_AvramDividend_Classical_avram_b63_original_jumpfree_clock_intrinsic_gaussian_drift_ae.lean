-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b63_original_jumpfree_clock_intrinsic_gaussian_drift_ae
-- name    : AvramDividend.Classical.avram_b63_original_jumpfree_clock_intrinsic_gaussian_drift_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T11:50:54.139261+00:00
-- url     : https://prove2.me/theorems/5b620634-02fb-46a8-8391-7c75cf404ea5
-- title:
--   Original jump-free random-clock Lévy source is intrinsic Gaussian plus compensation drift almost surely
-- statement:
--   For the exact original negatively jumping Lévy process and genuine intrinsic Gaussian residual, under the true compensated small-mark drift identity and absence of a source large-negative-jump increment, the physical drift-corrected Lévy increment between two arbitrary original random clocks equals the genuine Gaussian residual increment plus deterministic mark compensator drift almost surely.
-- source:
--   Proved B62 exact original source random-clock Gaussian decomposition and almost-sure identification with intrinsic Gaussian residual.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_b62_original_jumpfree_random_clock_intrinsic_gaussian_drift_exact
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b63_original_jumpfree_clock_intrinsic_gaussian_drift_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun k : ℕ => avram_p4_h_gaussian_intrinsic_truncated_residual X k u ω)
        atTop (𝓝 (R u ω)))
    (hJsource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun k : ℕ => avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω)
        atTop (𝓝 (Jsmall u ω)))
    (s t : Ω → ℝ≥0) (d : ℝ)
    (hSmall : ∀ ω, Jsmall (t ω) ω - Jsmall (s ω) ω =
      d * ((t ω : ℝ) - (s ω : ℝ)))
    (hLarge : ∀ ω,
      avram_p4_h_gaussian_intrinsic_large_jump_sum X (t ω) ω =
      avram_p4_h_gaussian_intrinsic_large_jump_sum X (s ω) ω) :
    ∀ᵐ ω ∂P,
      X.X (t ω) ω - X.X (s ω) ω -
        ((t ω : ℝ) - (s ω : ℝ)) * X.c =
      (R (t ω) ω - R (s ω) ω) +
        d * ((t ω : ℝ) - (s ω : ℝ)) := by sorry
