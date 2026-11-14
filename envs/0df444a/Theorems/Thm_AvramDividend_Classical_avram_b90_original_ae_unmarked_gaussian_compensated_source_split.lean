-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b90_original_ae_unmarked_gaussian_compensated_source_split
-- name    : AvramDividend.Classical.avram_b90_original_ae_unmarked_gaussian_compensated_source_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T14:20:56.95427+00:00
-- url     : https://prove2.me/theorems/34316881-7de9-4f5c-93f0-c41d4dade30f
-- title:
--   Same-original-space stopped Gaussian residual source split with almost-everywhere unmarked cell assumptions
-- statement:
--   Use Proved original jb20 source identity for all random-clock endpoints to construct M equal almost everywhere to original intrinsic Gaussian residual R. On the joint conull event where the selected unmarked source cells have exactly the prescribed compensated negative small-band drift and constant original large negative-jump sum, cancel those original source terms. This yields the exact random-cell Gaussian/drift split on that same conull event. Unlike B78, hSmall and hLarge are only required almost everywhere, compatible with the canonical Jsmall source cutoff convergence and valid stochastic localisation. No independent Gaussian process nor global negative-mark second moment is assumed.
-- source:
--   Avram Palmowski Pistorius Proposition 4(i), Proved avram_jb20_original_physical_random_clock_increment_split, physical small/large-negative-mark source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_jb20_original_physical_random_clock_increment_split
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original a.e. stopped unmarked source cells split into intrinsic Gaussian residual and compensated negative-mark drift. -/

theorem AvramDividend.Classical.avram_b90_original_ae_unmarked_gaussian_compensated_source_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (𝓝 (R t ω)))
    (hJsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (𝓝 (Jsmall t ω)))
    (S : Finset ℕ) (s t : ℕ → Ω → ℝ≥0)
    (J : Ω → Finset ℕ) (d : ℝ)
    (hOrdered : ∀ ω i, i ∈ S → s i ω ≤ t i ω)
    (hSmall : ∀ᵐ ω ∂P, ∀ i, i ∈ S → i ∉ J ω →
      Jsmall (t i ω) ω - Jsmall (s i ω) ω =
        d * (((t i ω - s i ω : ℝ≥0) : ℝ)))
    (hLarge : ∀ᵐ ω ∂P, ∀ i, i ∈ S → i ∉ J ω →
      avram_p4_h_gaussian_intrinsic_large_jump_sum X (t i ω) ω =
      avram_p4_h_gaussian_intrinsic_large_jump_sum X (s i ω) ω) :
    ∃ M : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂P, ∀ u : ℝ≥0, M u ω = R u ω) ∧
      (∀ᵐ ω ∂P, ∀ i, i ∈ S → i ∉ J ω →
        X.X (t i ω) ω - X.X (s i ω) ω -
          ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c =
        (M (t i ω) ω - M (s i ω) ω) +
          d * ((t i ω - s i ω : ℝ≥0) : ℝ)) := by sorry
