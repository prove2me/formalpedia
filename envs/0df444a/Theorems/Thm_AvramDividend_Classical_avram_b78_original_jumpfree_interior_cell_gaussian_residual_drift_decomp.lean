-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b78_original_jumpfree_interior_cell_gaussian_residual_drift_decomp
-- name    : AvramDividend.Classical.avram_b78_original_jumpfree_interior_cell_gaussian_residual_drift_decomp
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T14:19:20.364961+00:00
-- url     : https://prove2.me/theorems/a9fd1e1b-7a61-4aef-9c5b-e1497d396548
-- title:
--   Original marked jumpfree random stopped cells have intrinsic Gaussian plus compensated drift source increment
-- statement:
--   This is the exact same-source random-clock no-jump increment identity needed to instantiate the hNoJump premise of B73/B75, without inventing an independent Gaussian process. The Proved jb20 original physical random clock source decomposition constructs a total original Gaussian residual M (equal almost everywhere to the intrinsic truncated source limit R) together with the original small compensated negative jump term and the original large negative jump sum, and proves their exact pathwise increments at any two random clocks. On each selected interior cell not marked by J, assume explicitly that the original small compensated jump increment is only the physical compensation drift times elapsed time, and that the original large negative jump sum does not change. The exact random-clock source identity then gives the physical drift-corrected X increment as the original intrinsic Gaussian increment plus the compensation drift. All times use the true source and filtration. This theorem does not pretend that arbitrary cells are jumpfree; establishing hSmall and hLarge from the actual original finite negative-jump point process and mark assignment is the next source obligation. It needs no global second mark moment.
-- source:
--   Proved jb20_original_physical_random_clock_increment_split, original B73/B75 noJump hypothesis and source finite-activity mark convention.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_jb20_original_physical_random_clock_increment_split
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b78_original_jumpfree_interior_cell_gaussian_residual_drift_decomp
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
    (hSmall : ∀ ω i, i ∈ S → i ∉ J ω →
      Jsmall (t i ω) ω - Jsmall (s i ω) ω =
        d * (((t i ω - s i ω : ℝ≥0) : ℝ)))
    (hLarge : ∀ ω i, i ∈ S → i ∉ J ω →
      avram_p4_h_gaussian_intrinsic_large_jump_sum X (t i ω) ω =
      avram_p4_h_gaussian_intrinsic_large_jump_sum X (s i ω) ω) :
    ∃ M : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂P, ∀ u : ℝ≥0, M u ω = R u ω) ∧
      (∀ ω i, i ∈ S → i ∉ J ω →
        X.X (t i ω) ω - X.X (s i ω) ω -
          ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c =
        (M (t i ω) ω - M (s i ω) ω) +
          d * ((t i ω - s i ω : ℝ≥0) : ℝ)) := by sorry
