-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b62_original_jumpfree_random_clock_intrinsic_gaussian_drift_exact
-- name    : AvramDividend.Classical.avram_b62_original_jumpfree_random_clock_intrinsic_gaussian_drift_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T11:44:49.247199+00:00
-- url     : https://prove2.me/theorems/d7e678c0-ea79-4ad5-9471-9d427289239a
-- title:
--   Original physical Lévy random-clock no-negative-jump increment equals intrinsic Gaussian residual plus finite-activity compensation drift
-- statement:
--   On the actual original spectrally negative Lévy path and filtration, form the total intrinsic Gaussian martingale M whose cutoff-residual equals the genuine intrinsic Gaussian source R almost everywhere at every time. For any two physical random clocks, if the physical compensated small-negative-jump source increment equals a stated deterministic duration drift and the actual large-negative-jump source sum has no increment, then the original drift-corrected X source increment equals the same-path intrinsic Gaussian increment plus exactly that duration drift, pointwise on every sample. No independent Gaussian proxy and no post-ruin continuation are used.
-- source:
--   Proved JB20 original physical random-clock Gaussian and compensated negative marked-jump decomposition, exact source path algebra under explicit no-jump small/large compensation hypotheses.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_jb20_original_physical_random_clock_increment_split
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b62_original_jumpfree_random_clock_intrinsic_gaussian_drift_exact
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
    ∃ M : ℝ≥0 → Ω → ℝ,
      (∀ ω,
        X.X (t ω) ω - X.X (s ω) ω -
          ((t ω : ℝ) - (s ω : ℝ)) * X.c =
        (M (t ω) ω - M (s ω) ω) +
          d * ((t ω : ℝ) - (s ω : ℝ))) ∧
      (∀ᵐ ω ∂P, ∀ u : ℝ≥0, M u ω = R u ω) := by sorry
